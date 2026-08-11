/-
  Small recursive-descent parser for symbolic expressions.

  Grammar (highest precedence last):

    expr     = sum
    sum      = product  { ('+' | '-') product }
    product  = unary    { ('*' | '/' | '·' | juxtapose) unary }
    unary    = ('+' | '-') unary | power
    power    = atom     [ '^' unary ]          -- right-associative; binds tighter than unary
    atom     = number | call_or_var | '(' expr ')'
    call     = ident '(' [expr { ',' expr }] ')'

  Juxtaposition denotes multiplication: `2x`, `(x+1)(x-2)`, `sin(x)cos(x)`.

  Built-in calls (desugared while parsing):
    sin, cos, tan, exp, ln, log, sqrt
    diff(e) | diff(e, v)     — differentiate
    int(e)  | int(e, v)      — integrate (fails if no antiderivative)
    simplify(e), expand(e)
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Normal
import Taschenrechner.Eval
import Taschenrechner.Numeric
import Taschenrechner.Solve
import Taschenrechner.Diff
import Taschenrechner.Integrate
import Taschenrechner.Series
import Taschenrechner.Limit
import Taschenrechner.Sum
import Taschenrechner.ODE
import Taschenrechner.Complex
import Taschenrechner.Matrix
import Taschenrechner.LinAlg
import Taschenrechner.Eigen
import Taschenrechner.Env

namespace Taschenrechner.Parse

open Taschenrechner
open Taschenrechner.Expr

/-! ### Tokens -/

inductive Token where
  | num   : RatConst → Token
  | ident : String → Token
  | plus | minus | star | slash | caret | middot
  | eq | lt | le | gt | ge
  | lparen | rparen | comma
  | lbracket | rbracket | semicolon
  | eof
  deriving Repr, DecidableEq, Inhabited

def Token.toString : Token → String
  | .num r => RatConst.toString r
  | .ident s => s
  | .plus => "+"
  | .minus => "-"
  | .star => "*"
  | .slash => "/"
  | .caret => "^"
  | .middot => "·"
  | .eq => "="
  | .lt => "<"
  | .le => "≤"
  | .gt => ">"
  | .ge => "≥"
  | .lparen => "("
  | .rparen => ")"
  | .comma => ","
  | .lbracket => "["
  | .rbracket => "]"
  | .semicolon => ";"
  | .eof => "<eof>"

instance : ToString Token where
  toString := Token.toString

/-! ### Character helpers -/

private def isAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

private def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

private def isIdentCont (c : Char) : Bool :=
  isAlpha c || isDigit c

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def charsToString (cs : List Char) : String :=
  String.ofList cs

/-- Local trim helper (avoids deprecated `String.trim` → `String.Slice`). -/
private partial def strTrim (s : String) : String :=
  let cs := s.toList.dropWhile isSpace
  let cs := cs.reverse.dropWhile isSpace |>.reverse
  charsToString cs

/-! ### Lexer -/

/-- Tokenize `input`. Returns `Except` with a human-readable error. -/
def tokenize (input : String) : Except String (Array Token) := do
  let cs := input.toList.toArray
  let mut i : Nat := 0
  let mut out : Array Token := #[]
  let len := cs.size
  while i < len do
    let c := cs[i]!
    if isSpace c then
      i := i + 1
    else if isDigit c || (c == '.' && i + 1 < len && isDigit cs[i + 1]!) then
      -- Integer or decimal literal → exact rational (1.5 → 3/2, .25 → 1/4)
      let start := i
      let mut intDigits : String := ""
      let mut fracDigits : String := ""
      if c == '.' then
        i := i + 1
        let fstart := i
        while i < len && isDigit cs[i]! do
          i := i + 1
        fracDigits := charsToString (cs.extract fstart i).toList
        intDigits := "0"
      else
        while i < len && isDigit cs[i]! do
          i := i + 1
        intDigits := charsToString (cs.extract start i).toList
        if i < len && cs[i]! == '.' then
          i := i + 1
          let fstart := i
          while i < len && isDigit cs[i]! do
            i := i + 1
          fracDigits := charsToString (cs.extract fstart i).toList
      match intDigits.toInt?, (if fracDigits.isEmpty then some (0 : Int) else fracDigits.toInt?) with
      | some ip, some fp =>
        if fracDigits.isEmpty then
          out := out.push (.num (RatConst.ofInt ip))
        else
          let k := fracDigits.length
          let den := Nat.pow 10 k
          let num : Int := ip * (den : Int) + (if ip < 0 then -fp else fp)
          out := out.push (.num (RatConst.normalize ⟨num, den⟩))
      | _, _ => throw s!"invalid number at position {start}"
    else if isAlpha c then
      let start := i
      i := i + 1
      while i < len && isIdentCont cs[i]! do
        i := i + 1
      -- Allow trailing prime(s): y', f'', yp remains yp
      while i < len && cs[i]! == '\'' do
        i := i + 1
      let name := charsToString (cs.extract start i).toList
      out := out.push (.ident name)
    else
      match c with
      | '+' => out := out.push .plus; i := i + 1
      | '-' => out := out.push .minus; i := i + 1
      | '*' => out := out.push .star; i := i + 1
      | '/' => out := out.push .slash; i := i + 1
      | '^' => out := out.push .caret; i := i + 1
      | '·' => out := out.push .middot; i := i + 1
      | '=' => out := out.push .eq; i := i + 1
      | '<' =>
        if i + 1 < len && cs[i + 1]! == '=' then
          out := out.push .le; i := i + 2
        else
          out := out.push .lt; i := i + 1
      | '>' =>
        if i + 1 < len && cs[i + 1]! == '=' then
          out := out.push .ge; i := i + 2
        else
          out := out.push .gt; i := i + 1
      | '≤' => out := out.push .le; i := i + 1
      | '≥' => out := out.push .ge; i := i + 1
      | '(' => out := out.push .lparen; i := i + 1
      | ')' => out := out.push .rparen; i := i + 1
      | ',' => out := out.push .comma; i := i + 1
      | '[' => out := out.push .lbracket; i := i + 1
      | ']' => out := out.push .rbracket; i := i + 1
      | ';' => out := out.push .semicolon; i := i + 1
      | _ => throw s!"unexpected character '{c}' at position {i}"
  pure (out.push .eof)

/-! ### Parser state -/

structure Parser where
  tokens : Array Token
  pos    : Nat
  deriving Repr

def Parser.peek (p : Parser) : Token :=
  p.tokens[p.pos]?.getD .eof

def Parser.advance (p : Parser) : Parser :=
  { p with pos := p.pos + 1 }

def Parser.expect (p : Parser) (t : Token) : Except String Parser := do
  if p.peek == t then pure p.advance
  else throw s!"expected '{t}', got '{p.peek}'"

/-- Does this token begin an atom (for juxtaposition)? -/
def Token.startsAtom : Token → Bool
  | .num _ | .ident _ | .lparen | .lbracket => true
  | _ => false

/-! ### Built-in calls (desugared during parse) -/

def asVarName (e : Expr) : Except String String :=
  match e with
  | .var v => pure v
  | _ => throw s!"expected a variable name, got expression '{e}'"

def integrateCall (e : Expr) (v : String) : Except String Expr :=
  match integrate e v with
  | .success F _ => pure F
  | .notElementary r => throw s!"not elementary: {r}"
  | .failure r => throw s!"integration failed: {r}"

def integrateDefiniteCall (e : Expr) (v : String) (lo hi : Expr) : Except String Expr :=
  match integrateDefinite e v lo hi with
  | .success r _ => pure r
  | .notElementary msg => throw s!"not elementary: {msg}"
  | .failure msg => throw s!"integration failed: {msg}"

/-- Desugar built-in function / CAS forms. -/
def applyCall (name : String) (args : List Expr) : Except String Expr := do
  let n := name.toLower
  match n, args with
  | "sin", [e] => pure (Expr.sin e)
  | "cos", [e] => pure (Expr.cos e)
  | "tan", [e] => pure (Expr.tan e)
  | "exp", [e] => pure (Expr.exp e)
  | "ln",  [e] => pure (Expr.ln e)
  | "log", [e] => pure (Expr.ln e)
  | "sqrt", [e] => pure (Taschenrechner.sqrt e)
  | "atan", [e] => pure (Expr.atan e)
  | "arctan", [e] => pure (Expr.atan e)
  | "re", [e] => pure (Expr.re e)
  | "im", [e] => pure (Expr.im e)
  | "conj", [e] => pure (Expr.conj e)
  | "abs", [e] =>
    -- |z| = sqrt(re(z)² + im(z)²)
    pure (Taschenrechner.sqrt (Expr.add
      (Expr.pow (Expr.re e) (2 : Expr))
      (Expr.pow (Expr.im e) (2 : Expr))))
  | "simplify", [e] => pure (simplify e)
  | "expand", [e] => pure (expand e)
  | "cancel", [e] => pure (cancel e)
  | "together", [e] => pure (together e)
  | "together", [e, v] => do
      let v ← asVarName v
      pure (together e v)
  | "nf", [e] | "normal", [e] | "normalform", [e] => pure (normalForm e)
  | "nf", [e, v] | "normal", [e, v] | "normalform", [e, v] => do
      let v ← asVarName v
      pure (normalForm e v)
  | "subst", [e, v, val] | "subs", [e, v, val] => do
      let v ← asVarName v
      pure (simplify (subst e v val))
  | "eval", [e] => pure (evalOrSimplify e)
  | "eval", [e, v, val] | "at", [e, v, val] => do
      let v ← asVarName v
      pure (evalAtOrSimplify e v val)
  -- "N" is lowercased to "n" here; only capital N is a builtin (see isBuiltinName)
  | "n", [e] | "numeric", [e] | "num", [e] =>
      N e 6
  | "n", [e, d] | "numeric", [e, d] | "num", [e, d] =>
      match asNatDim d with
      | some k => N e k
      | none => throw "N: expected non-negative integer digit count"
  | "euler", [e] => pure (eulerExpand e)
  | "det", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.det rows with
      | some d => pure (simplify d)
      | none => throw "det: expected square matrix"
    | none => throw "det: expected a matrix"
  | "trace", [e] | "tr", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.trace rows with
      | some t => pure (simplify t)
      | none => throw "trace: expected square matrix"
    | none => throw "trace: expected a matrix"
  | "transpose", [e] | "tp", [e] =>
    match asMat? e with
    | some rows => pure (Expr.mat (Mat.transpose rows))
    | none => throw "transpose: expected a matrix"
  | "inv", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.inv rows with
      | some inv => pure (simplify (Expr.mat inv))
      | none => throw "inv: singular or non-square matrix"
    | none => throw "inv: expected a matrix"
  | "rref", [e] =>
    match asMat? e with
    | some rows => pure (simplify (Expr.mat (Mat.rref rows)))
    | none => throw "rref: expected a matrix"
  | "rank", [e] =>
    match asMat? e with
    | some rows => pure (Expr.ofNat (Mat.rank rows))
    | none => throw "rank: expected a matrix"
  | "nullity", [e] =>
    match asMat? e with
    | some rows => pure (Expr.ofNat (Mat.nullity rows))
    | none => throw "nullity: expected a matrix"
  | "nullspace", [e] | "null", [e] | "ker", [e] =>
    match asMat? e with
    | some rows =>
      let N := Mat.nullspace rows
      if N.isEmpty then
        -- trivial nullspace: return  n×0 as empty mat is awkward; use zeros(n,0) empty rows
        let n := Mat.ncols rows
        pure (Expr.mat (Array.replicate n #[]))
      else
        pure (simplify (Expr.mat N))
    | none => throw "nullspace: expected a matrix"
  | "charpoly", [e] | "characteristic", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.charpoly rows with
      | some p => pure p
      | none => throw "charpoly: expected square matrix"
    | none => throw "charpoly: expected a matrix"
  | "charpoly", [e, v] | "characteristic", [e, v] => do
      let v ← asVarName v
      match asMat? e with
      | some rows =>
        match Mat.charpoly rows v with
        | some p => pure p
        | none => throw "charpoly: expected square matrix"
      | none => throw "charpoly: expected a matrix"
  | "eigvals", [e] | "eigenvalues", [e] | "eigen", [e] | "eig", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.eigenvaluesMat rows with
      | some m => pure (simplify (Expr.mat m))
      | none => throw "eigvals: expected square matrix"
    | none => throw "eigvals: expected a matrix"
  | "eigenspace", [e, lam] | "eigenvectors", [e, lam] | "eigvec", [e, lam] =>
    match asMat? e with
    | some rows =>
      match Mat.eigenspace rows lam with
      | some N =>
        if N.isEmpty then
          let n := Mat.ncols rows
          pure (Expr.mat (Array.replicate n #[]))
        else
          pure (simplify (Expr.mat N))
      | none => throw "eigenspace: expected square matrix"
    | none => throw "eigenspace: expected a matrix"
  | "diagonalize", [e] | "diag", [e] | "diagonalise", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.diagonalize rows |>.toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"diagonalize: {msg}"
    | none => throw "diagonalize: expected a matrix"
  | "modal", [e] | "eigenmatrix", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.modalMatrix rows with
      | .ok P => pure (simplify (Expr.mat P))
      | .error msg => throw s!"modal: {msg}"
    | none => throw "modal: expected a matrix"
  | "diagform", [e] | "diagonalform", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.diagonalForm rows with
      | .ok D => pure (simplify (Expr.mat D))
      | .error msg => throw s!"diagform: {msg}"
    | none => throw "diagform: expected a matrix"
  | "expm", [e] | "matexp", [e] =>
    match asMat? e with
    | some rows =>
      match Mat.expm rows with
      | .ok R => pure (simplify (Expr.mat R))
      | .error msg => throw s!"expm: {msg}"
    | none => throw "expm: expected a matrix"
  | "solve", args => do
      solveDispatch args
  | "roots", [e] =>
    let v := Expr.primaryVar e
    pure (Expr.mat #[(roots e v).toArray])
  | "roots", [e, v] => do
      let v ← asVarName v
      pure (Expr.mat #[(roots e v).toArray])
  | "factor", [e] =>
    pure (factor e (Expr.primaryVar e))
  | "factor", [e, v] => do
      let v ← asVarName v
      pure (factor e v)
  | "collect", [e] => pure (collect e (Expr.primaryVar e))
  | "collect", [e, v] => do
      let v ← asVarName v
      pure (collect e v)
  | "apart", [e] | "pf", [e] | "partialfractions", [e] =>
      pure (apartOrSimplify e (Expr.primaryVar e))
  | "apart", [e, v] | "pf", [e, v] | "partialfractions", [e, v] => do
      let v ← asVarName v
      pure (apartOrSimplify e v)
  | "coeff", [e, n] =>
    match asNatDim n with
    | some k =>
      match coeffOf e (Expr.primaryVar e) k with
      | some c => pure c
      | none => throw "coeff: expression is not polynomial/rational in its free variable"
    | none => throw "coeff: expected non-negative integer degree"
  | "coeff", [e, v, n] => do
      let v ← asVarName v
      match asNatDim n with
      | some k =>
        match coeffOf e v k with
        | some c => pure c
        | none => throw s!"coeff: expression is not polynomial/rational in {v}"
      | none => throw "coeff: expected non-negative integer degree"
  | "eye", [e] =>
    match asNatDim e with
    | some n => pure (Expr.mat (Mat.eye n))
    | none => throw "eye: expected non-negative integer dimension"
  | "zeros", [e] =>
    match asNatDim e with
    | some n => pure (Expr.mat (Mat.zeros n n))
    | none => throw "zeros: expected integer size"
  | "zeros", [e, f] =>
    match asNatDim e, asNatDim f with
    | some m, some n => pure (Expr.mat (Mat.zeros m n))
    | _, _ => throw "zeros: expected integer dimensions"
  | "ones", [e] =>
    match asNatDim e with
    | some n => pure (Expr.mat (Mat.ones n n))
    | none => throw "ones: expected integer size"
  | "ones", [e, f] =>
    match asNatDim e, asNatDim f with
    | some m, some n => pure (Expr.mat (Mat.ones m n))
    | _, _ => throw "ones: expected integer dimensions"
  | "diff", [e] => pure (diff e "x")
  | "diff", [e, v] => do
      let v ← asVarName v
      pure (diff e v)
  | "d", [e] => pure (diff e "x")
  | "d", [e, v] => do
      let v ← asVarName v
      pure (diff e v)
  | "int", [e] => integrateCall e "x"
  | "int", [e, v] => do
      let v ← asVarName v
      integrateCall e v
  | "int", [e, lo, hi] =>
      -- definite ∫_lo^hi e dx
      integrateDefiniteCall e "x" lo hi
  | "int", [e, v, lo, hi] => do
      let v ← asVarName v
      integrateDefiniteCall e v lo hi
  | "integrate", [e] => integrateCall e "x"
  | "integrate", [e, v] => do
      let v ← asVarName v
      integrateCall e v
  | "integrate", [e, lo, hi] =>
      integrateDefiniteCall e "x" lo hi
  | "integrate", [e, v, lo, hi] => do
      let v ← asVarName v
      integrateDefiniteCall e v lo hi
  | "taylor", [e, n] =>
      match asNatDim n with
      | some k => pure (taylor e "x" zero k)
      | none => throw "taylor: expected non-negative integer order"
  | "taylor", [e, v, n] => do
      -- taylor(f, x, n) about 0, or taylor(f, a, n) about a in x if v not a var
      match asVarName v with
      | .ok name =>
        match asNatDim n with
        | some k => pure (taylor e name zero k)
        | none => throw "taylor: expected non-negative integer order"
      | .error _ =>
        match asNatDim n with
        | some k => pure (taylor e "x" v k)
        | none => throw "taylor: expected non-negative integer order"
  | "taylor", [e, v, a, n] => do
      let v ← asVarName v
      match asNatDim n with
      | some k => pure (taylor e v a k)
      | none => throw "taylor: expected non-negative integer order"
  | "maclaurin", [e, n] | "series", [e, n] =>
      match asNatDim n with
      | some k => pure (maclaurin e "x" k)
      | none => throw s!"{name}: expected non-negative integer order"
  | "maclaurin", [e, v, n] | "series", [e, v, n] => do
      let v ← asVarName v
      match asNatDim n with
      | some k => pure (maclaurin e v k)
      | none => throw s!"{name}: expected non-negative integer order"
  | "laurent", [e, n] =>
      match asNatDim n with
      | some k => laurent e "x" zero k
      | none => throw "laurent: expected non-negative integer order"
  | "laurent", [e, a, n] => do
      -- laurent(f, a, n) about a in x, or laurent(f, x, n) about 0
      match asVarName a, asNatDim n with
      | .ok v, some k => laurent e v zero k
      | _, some k => laurent e "x" a k
      | _, none => throw "laurent: expected non-negative integer order"
  | "laurent", [e, v, a, n] => do
      let v ← asVarName v
      match asNatDim n with
      | some k => laurent e v a k
      | none => throw "laurent: expected non-negative integer order"
  | "seriesadd", [f, g, n] | "sadd", [f, g, n] =>
      match asNatDim n with
      | some k => seriesAdd f g "x" zero k
      | none => throw "seriesadd: expected non-negative integer order"
  | "seriesadd", [f, g, a, n] | "sadd", [f, g, a, n] =>
      match asNatDim n with
      | some k => seriesAdd f g "x" a k
      | none => throw "seriesadd: expected non-negative integer order"
  | "seriesmul", [f, g, n] | "smul", [f, g, n] =>
      match asNatDim n with
      | some k => seriesMul f g "x" zero k
      | none => throw "seriesmul: expected non-negative integer order"
  | "seriesmul", [f, g, a, n] | "smul", [f, g, a, n] =>
      match asNatDim n with
      | some k => seriesMul f g "x" a k
      | none => throw "seriesmul: expected non-negative integer order"
  | "limit", [e, a] | "lim", [e, a] =>
      -- default variable x, two-sided
      match (limitAt e "x" a).toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"limit: {msg}"
  | "limit", [e, v, a] | "lim", [e, v, a] => do
      -- limit(e, x, a) two-sided, or limit(e, a, side) with default x
      match asVarName v with
      | .ok name =>
        match (limitAt e name a).toExpr? with
        | .ok r => pure r
        | .error msg => throw s!"limit: {msg}"
      | .error _ =>
        match LimitSide.ofExpr? a with
        | some side =>
          -- limit(e, point, side) — second arg was point, third was side
          match (limitAt e "x" v side).toExpr? with
          | .ok r => pure r
          | .error msg => throw s!"limit: {msg}"
        | none =>
          let v ← asVarName v
          match (limitAt e v a).toExpr? with
          | .ok r => pure r
          | .error msg => throw s!"limit: {msg}"
  | "limit", [e, v, a, sideE] | "lim", [e, v, a, sideE] => do
      let v ← asVarName v
      match LimitSide.ofExpr? sideE with
      | some side =>
        match (limitAt e v a side).toExpr? with
        | .ok r => pure r
        | .error msg => throw s!"limit: {msg}"
      | none => throw "limit: side must be 1/right or -1/left"
  | "limleft", [e, a] | "limitleft", [e, a] =>
      match (limitLeft e "x" a).toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"limit: {msg}"
  | "limleft", [e, v, a] | "limitleft", [e, v, a] => do
      let v ← asVarName v
      match (limitLeft e v a).toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"limit: {msg}"
  | "limright", [e, a] | "limitright", [e, a] =>
      match (limitRight e "x" a).toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"limit: {msg}"
  | "limright", [e, v, a] | "limitright", [e, v, a] => do
      let v ← asVarName v
      match (limitRight e v a).toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"limit: {msg}"
  | "poleorder", [e, a] | "ord", [e, a] =>
      pure (poleOrderExpr e "x" a)
  | "poleorder", [e, v, a] | "ord", [e, v, a] => do
      let v ← asVarName v
      pure (poleOrderExpr e v a)
  | "classify", [e, a] | "singularity", [e, a] =>
      match (classifyAt e "x" a).toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"classify: {msg}"
  | "classify", [e, v, a] | "singularity", [e, v, a] => do
      let v ← asVarName v
      match (classifyAt e v a).toExpr? with
      | .ok r => pure r
      | .error msg => throw s!"classify: {msg}"
  | "sum", [a, b, c, d] => do
      -- sum(expr, k, lo, hi) or sum(k, lo, hi, expr)
      match asVarName a, asVarName b with
      | .ok k, .error _ =>
        -- sum(k, lo, hi, body)
        sumFiniteExpr d k b c
      | .error _, .ok k =>
        -- sum(body, k, lo, hi)
        sumFiniteExpr a k c d
      | .ok k1, .ok k2 =>
        -- both variables: prefer sum(k, lo, hi, body) if d depends on k1
        if dependsOn d k1 then sumFiniteExpr d k1 b c
        else if dependsOn a k2 then sumFiniteExpr a k2 c d
        else sumFiniteExpr d k1 b c
      | .error _, .error _ =>
        throw "sum: expected a free index variable (sum(expr, k, lo, hi) or sum(k, lo, hi, expr))"
  | "dsolve", [e] =>
      -- scalar ODE, or square matrix A for Y' = A Y
      match asMat? e with
      | some A => dsolveLinSys A "x"
      | none => dsolve e "y" "x"
  | "dsolve", [e, a] => do
      match asMat? e, asMat? a with
      | some A, some Y0 => dsolveLinSysIC A Y0 "x"
      | _, _ =>
        let y ← asVarName a
        dsolve e y "x"
  | "dsolve", [e, a, b] => do
      -- dsolve(eq, y, x)  OR  dsolve(eq, x0, y0) for y(x0)=y0
      match asVarName a, asVarName b with
      | .ok y, .ok x => dsolve e y x
      | _, _ => dsolveIC e "y" "x" a b
  | "dsolve", [e, a, b, c] => do
      -- dsolve(eq, y, x0, y0)  OR  dsolve(eq, x0, y0, yp0) second-order IC
      match asVarName a with
      | .ok y => dsolveIC e y "x" b c
      | .error _ => dsolveIC2 e "y" "x" a b c
  | "dsolve", [e, y, x, x0, y0] => do
      let y ← asVarName y
      let x ← asVarName x
      dsolveIC e y x x0 y0
  | "dsolve", [e, y, x, x0, y0, yp0] => do
      let y ← asVarName y
      let x ← asVarName x
      dsolveIC2 e y x x0 y0 yp0
  | "sin", _ | "cos", _ | "tan", _ | "exp", _ | "ln", _ | "log", _ | "sqrt", _
  | "atan", _ | "arctan", _ | "re", _ | "im", _ | "conj", _ | "abs", _
  | "simplify", _ | "expand", _ | "euler", _ | "cancel", _
  | "det", _ | "trace", _ | "tr", _ | "transpose", _ | "tp", _ | "inv", _
  | "rref", _ | "rank", _ | "nullity", _ | "nullspace", _ | "null", _ | "ker", _ | "eye", _ =>
      throw s!"{name} expects 1 argument, got {args.length}"
  | "zeros", _ | "ones", _ | "together", _ | "nf", _ | "normal", _ | "normalform", _
  | "roots", _ | "factor", _ | "collect", _ | "charpoly", _ | "characteristic", _
  | "apart", _ | "pf", _ | "partialfractions", _ =>
      throw s!"{name} expects 1 or 2 arguments, got {args.length}"
  | "eigvals", _ | "eigenvalues", _ | "eigen", _ | "eig", _ =>
      throw s!"{name} expects 1 argument (square matrix), got {args.length}"
  | "eigenspace", _ | "eigenvectors", _ | "eigvec", _ =>
      throw s!"{name} expects 2 arguments (matrix, eigenvalue), got {args.length}"
  | "diagonalize", _ | "diag", _ | "diagonalise", _ | "modal", _ | "eigenmatrix", _
  | "diagform", _ | "diagonalform", _ | "expm", _ | "matexp", _ =>
      throw s!"{name} expects 1 argument (square matrix), got {args.length}"
  | "coeff", _ =>
      throw s!"coeff expects coeff(e, n) or coeff(e, v, n), got {args.length} args"
  | "diff", _ | "d", _ =>
      throw s!"{name} expects 1 or 2 arguments, got {args.length}"
  | "int", _ | "integrate", _ =>
      throw s!"{name} expects int(f) | int(f,x) | int(f,a,b) | int(f,x,a,b), got {args.length} args"
  | "taylor", _ =>
      throw s!"taylor expects taylor(f,n) | taylor(f,x,n) | taylor(f,a,n) | taylor(f,x,a,n), got {args.length} args"
  | "maclaurin", _ | "series", _ =>
      throw s!"{name} expects {name}(f,n) or {name}(f,x,n), got {args.length} args"
  | "laurent", _ =>
      throw s!"laurent expects laurent(f,n) | laurent(f,a,n) | laurent(f,x,a,n), got {args.length} args"
  | "seriesadd", _ | "sadd", _ =>
      throw s!"seriesadd expects seriesadd(f,g,n) or seriesadd(f,g,a,n), got {args.length} args"
  | "seriesmul", _ | "smul", _ =>
      throw s!"seriesmul expects seriesmul(f,g,n) or seriesmul(f,g,a,n), got {args.length} args"
  | "limit", _ | "lim", _ =>
      throw s!"{name} expects limit(e,a) | limit(e,x,a) | limit(e,a,side) | limit(e,x,a,side), got {args.length} args"
  | "limleft", _ | "limitleft", _ | "limright", _ | "limitright", _ =>
      throw s!"{name} expects 2 or 3 arguments, got {args.length}"
  | "poleorder", _ | "ord", _ | "classify", _ | "singularity", _ =>
      throw s!"{name} expects 2 or 3 arguments, got {args.length}"
  | "sum", _ =>
      throw s!"sum expects sum(expr, k, lo, hi) or sum(k, lo, hi, expr), got {args.length} args"
  | "dsolve", _ =>
      throw s!"dsolve expects dsolve(eq)|dsolve(A)|dsolve(A,Y0)|dsolve(eq,x0,y0)|dsolve(eq,x0,y0,yp0)|… (y'/yp/y''/ypp), got {args.length} args"
  | "subst", _ | "subs", _ =>
      throw s!"{name} expects 3 arguments: subst(expr, var, value), got {args.length}"
  | "eval", _ | "at", _ =>
      throw s!"{name} expects 1 or 3 arguments: eval(expr) or eval(expr, var, value), got {args.length}"
  | "n", _ | "numeric", _ | "num", _ =>
      throw s!"{name} expects N(e) or N(e, digits), got {args.length} args"
  | _, _ =>
      throw s!"unknown function '{name}'"
where
  asNatDim : Expr → Option Nat
    | .const c =>
      match CplxConst.toRat? c with
      | some q =>
        if q.den == 1 && q.num ≥ 0 then some q.num.toNat else none
      | none => none
    | _ => none
  /-- Is this a bare variable name? -/
  isVar : Expr → Bool
    | .var _ => true
    | _ => false
  /-- Equation or inequality relation? -/
  isRel : Expr → Bool
    | .eq _ _ | .lt _ _ | .le _ _ => true
    | _ => false
  /-- Dispatch solve for all arities. -/
  solveDispatch (args : List Expr) : Except String Expr := do
    match args with
    | [] => throw "solve: expected arguments"
    | [e] =>
      -- scalar equation/inequality/residual in primary free var
      let v := Expr.primaryVar (match relationToResidual e with
        | some (_, r) => r
        | none => e)
      solveRelation e v
    | [a, b] =>
      match asMat? a, asMat? b with
      | some A, some B =>
        match Mat.solve A B with
        | .unique x => pure (simplify (Expr.mat x))
        | .general x _k => pure (simplify (Expr.mat x))
        | .inconsistent msg => throw s!"solve: {msg}"
        | .error msg => throw s!"solve: {msg}"
      | _, _ =>
        if isVar b then
          let v ← asVarName b
          solveRelation a v
        else if isRel a && isRel b then
          -- 2-equation system
          solveLinearSystem [a, b] none
        else
          -- treat as two residuals of a system, or lhs,rhs without var
          solveLinearSystem [a, b] none
    | [lhs, rhs, v] =>
      if isVar v && !isRel lhs then
        -- solve(lhs, rhs, x) equation
        let v ← asVarName v
        solveEqExpr? lhs rhs v
      else if isRel lhs && isRel rhs && isVar v then
        -- solve(eq1, eq2, x) — underdetermined naming, still 2 eqs
        let _ ← asVarName v
        solveLinearSystem [lhs, rhs] none
      else
        -- 3-equation system (or mix)
        solveLinearSystem [lhs, rhs, v] none
    | args =>
      -- Peel trailing variable names from the argument list.
      let (eqs, varNames) :=
        Id.run do
          let mut es := args
          let mut vs : List String := []
          let mut done := false
          while !done && !es.isEmpty do
            match es.getLast? with
            | some e =>
              if isVar e then
                match asVarName e with
                | .ok name =>
                  vs := name :: vs
                  es := es.dropLast
                | .error _ => done := true
              else done := true
            | none => done := true
          pure (es, vs)
      if eqs.isEmpty then throw "solve: no equations in system"
      else if eqs.length == 1 && varNames.length == 1 then
        solveRelation eqs[0]! varNames[0]!
      else if eqs.all isRel || eqs.length ≥ 2 then
        let vars? := if varNames.isEmpty then none else some varNames
        -- inequalities in multi-eq not supported
        if eqs.any fun e =>
            match e with
            | .lt _ _ | .le _ _ => true
            | _ => false
        then
          if eqs.length == 1 then
            solveRelation eqs[0]! (varNames.headD (Expr.primaryVar eqs[0]!))
          else
            throw "solve: systems of inequalities are not supported"
        else
          solveLinearSystem eqs vars?
      else
        solveLinearSystem eqs (if varNames.isEmpty then none else some varNames)

/-- Known callables that consume `(...)`; bare vars juxtapose: `x(x+1)` = `x*(x+1)`. -/
def isBuiltinName (name : String) : Bool :=
  let n := name.toLower
  n == "sin" || n == "cos" || n == "tan" || n == "exp" || n == "ln" || n == "log"
    || n == "sqrt" || n == "atan" || n == "arctan" || n == "re" || n == "im" || n == "conj"
    || n == "abs" || n == "simplify" || n == "expand" || n == "cancel"
    || n == "together" || n == "nf" || n == "normal" || n == "normalform"
    || n == "subst" || n == "subs" || n == "eval" || n == "at"
    || name == "N" || n == "numeric" || n == "num"  -- "N" only (not bare `n`)
    || n == "factor" || n == "roots" || n == "collect" || n == "coeff"
    || n == "apart" || n == "pf" || n == "partialfractions"
    || n == "taylor" || n == "maclaurin" || n == "series" || n == "laurent"
    || n == "seriesadd" || n == "sadd" || n == "seriesmul" || n == "smul"
    || n == "limit" || n == "lim" || n == "limleft" || n == "limitleft"
    || n == "limright" || n == "limitright" || n == "poleorder" || n == "ord"
    || n == "classify" || n == "singularity"
    || n == "sum" || n == "dsolve"
    || n == "diff" || n == "d" || n == "int" || n == "integrate" || n == "euler"
    || n == "det" || n == "trace" || n == "tr" || n == "transpose" || n == "tp" || n == "inv"
    || n == "rref" || n == "rank" || n == "solve" || n == "nullspace" || n == "null"
    || n == "ker" || n == "nullity"
    || n == "charpoly" || n == "characteristic"
    || n == "eigvals" || n == "eigenvalues" || n == "eigen" || n == "eig"
    || n == "eigenspace" || n == "eigenvectors" || n == "eigvec"
    || n == "diagonalize" || n == "diag" || n == "diagonalise" || n == "modal"
    || n == "eigenmatrix" || n == "diagform" || n == "diagonalform"
    || n == "expm" || n == "matexp"
    || n == "eye" || n == "zeros" || n == "ones" || n == "matrix" || n == "mat"

/-! ### Recursive-descent parsing (environment-aware) -/

mutual

/-- Lowest precedence: optional relation `lhs (=|<|>|<=|>=) rhs`. -/
partial def parseExpr (env : Env) (p : Parser) : Except String (Expr × Parser) := do
  let (lhs, p) ← parseSum env p
  match p.peek with
  | .eq =>
    let (rhs, p) ← parseSum env p.advance
    pure (Expr.eq lhs rhs, p)
  | .lt =>
    let (rhs, p) ← parseSum env p.advance
    pure (Expr.lt lhs rhs, p)
  | .le =>
    let (rhs, p) ← parseSum env p.advance
    pure (Expr.le lhs rhs, p)
  | .gt =>
    let (rhs, p) ← parseSum env p.advance
    pure (Expr.lt rhs lhs, p)  -- a > b → b < a
  | .ge =>
    let (rhs, p) ← parseSum env p.advance
    pure (Expr.le rhs lhs, p)  -- a ≥ b → b ≤ a
  | _ => pure (lhs, p)

partial def parseSum (env : Env) (p : Parser) : Except String (Expr × Parser) := do
  let (lhs, p) ← parseProduct env p
  go lhs p
where
  go (lhs : Expr) (p : Parser) : Except String (Expr × Parser) := do
    match p.peek with
    | .plus =>
      let (rhs, p) ← parseProduct env p.advance
      go (Expr.add lhs rhs) p
    | .minus =>
      let (rhs, p) ← parseProduct env p.advance
      go (Expr.sub lhs rhs) p
    | _ => pure (lhs, p)

partial def parseProduct (env : Env) (p : Parser) : Except String (Expr × Parser) := do
  let (lhs, p) ← parseUnary env p
  go lhs p
where
  go (lhs : Expr) (p : Parser) : Except String (Expr × Parser) := do
    match p.peek with
    | .star | .middot =>
      let (rhs, p) ← parseUnary env p.advance
      go (Expr.mul lhs rhs) p
    | .slash =>
      let (rhs, p) ← parseUnary env p.advance
      go (Expr.div lhs rhs) p
    | t =>
      if t.startsAtom then
        let (rhs, p) ← parseUnary env p
        go (Expr.mul lhs rhs) p
      else
        pure (lhs, p)

/-- Unary binds looser than `^`, so `-x^2` = `-(x^2)`. -/
partial def parseUnary (env : Env) (p : Parser) : Except String (Expr × Parser) := do
  match p.peek with
  | .plus => parseUnary env p.advance
  | .minus =>
    let (e, p) ← parseUnary env p.advance
    pure (Expr.neg e, p)
  | _ => parsePower env p

/-- Right-associative exponentiation: `a^b^c` = `a^(b^c)`. -/
partial def parsePower (env : Env) (p : Parser) : Except String (Expr × Parser) := do
  let (lhs, p) ← parseAtom env p
  match p.peek with
  | .caret =>
    let (rhs, p) ← parseUnary env p.advance
    pure (Expr.pow lhs rhs, p)
  | _ => pure (lhs, p)

partial def parseAtom (env : Env) (p : Parser) : Except String (Expr × Parser) := do
  match p.peek with
  | .num r => pure (Expr.ofRat r, p.advance)
  | .ident name => parseIdent env name p.advance
  | .lparen =>
    let (e, p) ← parseExpr env p.advance
    let p ← p.expect .rparen
    pure (e, p)
  | .lbracket =>
    parseMatrixBody env p.advance .rbracket
  | t => throw s!"expected number, identifier, '(', or '[', got '{t}'"

/--
  Parse matrix body until `closer` (`)` or `]`).
  Rows separated by `;`, entries by `,`.
-/
partial def parseMatrixBody (env : Env) (p : Parser) (closer : Token) : Except String (Expr × Parser) := do
  if p.peek == closer then
    throw "empty matrix"
  let (rows, p) ← parseMatrixRows env p closer
  let p ← p.expect closer
  match Mat.ofLists rows with
  | .error err => throw err
  | .ok data => pure (Expr.mat data, p)

partial def parseMatrixRows (env : Env) (p : Parser) (closer : Token) :
    Except String (List (List Expr) × Parser) := do
  let (row, p) ← parseMatrixRow env p closer
  match p.peek with
  | .semicolon =>
    let (rest, p) ← parseMatrixRows env p.advance closer
    pure (row :: rest, p)
  | t =>
    if t == closer then pure ([row], p)
    else throw s!"expected ';' or '{closer}' in matrix, got '{t}'"

partial def parseMatrixRow (env : Env) (p : Parser) (closer : Token) :
    Except String (List Expr × Parser) := do
  let (e, p) ← parseExpr env p
  go [e] p
where
  go (acc : List Expr) (p : Parser) : Except String (List Expr × Parser) := do
    match p.peek with
    | .comma =>
      let (e, p) ← parseExpr env p.advance
      go (acc ++ [e]) p
    | .semicolon => pure (acc, p)
    | t =>
      if t == closer then pure (acc, p)
      else throw s!"expected ',', ';', or '{closer}' in matrix row, got '{t}'"

partial def parseIdent (env : Env) (name : String) (p : Parser) : Except String (Expr × Parser) := do
  let lower := name.toLower
  if p.peek == .lparen && (lower == "matrix" || lower == "mat") then
    parseMatrixBody env p.advance .rparen
  else if p.peek == .lparen && isBuiltinName name then
    let (args, p) ← parseArgList env p.advance
    let e ← applyCall name args
    pure (e, p)
  else if name == "i" || name == "I" then
    pure (Expr.I, p)
  else if let some val := env.get? name then
    -- Session binding (must not shadow function calls above)
    pure (val, p)
  else
    pure (Expr.var name, p)

partial def parseArgList (env : Env) (p : Parser) : Except String (List Expr × Parser) := do
  if p.peek == .rparen then
    pure ([], p.advance)
  else
    let (e, p) ← parseExpr env p
    let (rest, p) ← parseArgListCont env p
    pure (e :: rest, p)

partial def parseArgListCont (env : Env) (p : Parser) : Except String (List Expr × Parser) := do
  match p.peek with
  | .comma =>
    let (e, p) ← parseExpr env p.advance
    let (rest, p) ← parseArgListCont env p
    pure (e :: rest, p)
  | .rparen => pure ([], p.advance)
  | t => throw s!"expected ',' or ')', got '{t}'"

end

/-! ### Public API -/

/-- Parse a full expression string under optional session `env`. -/
def parse (input : String) (env : Env := {}) : Except String Expr := do
  let tokens ← tokenize input
  let p : Parser := { tokens, pos := 0 }
  if p.peek == .eof then
    throw "empty expression"
  let (e, p) ← parseExpr env p
  match p.peek with
  | .eof => pure (simplify e)
  | t => throw s!"unexpected token '{t}' after expression"

/-- Parse without simplifying (useful for debugging the AST). -/
def parseRaw (input : String) (env : Env := {}) : Except String Expr := do
  let tokens ← tokenize input
  let p : Parser := { tokens, pos := 0 }
  if p.peek == .eof then
    throw "empty expression"
  let (e, p) ← parseExpr env p
  match p.peek with
  | .eof => pure e
  | t => throw s!"unexpected token '{t}' after expression"

/-- CLI-oriented top-level commands. -/
inductive Command where
  | expr      : Expr → Command
  | diff      : Expr → String → Command
  | integrate : Expr → String → Command
  | simplify  : Expr → Command
  | expand    : Expr → Command
  | cancel    : Expr → Command
  | together  : Expr → Command
  | normal    : Expr → Command
  | assign    : String → Expr → Command
  | vars      : Command
  | clearAll  : Command
  | clearOne  : String → Command
  | save      : String → Command
  | load      : String → Command
  | help      : Command
  deriving Repr

private def isKeyword (k : String) : Bool :=
  k == "diff" || k == "d" || k == "int" || k == "integrate"
    || k == "simplify" || k == "expand" || k == "cancel" || k == "together"
    || k == "nf" || k == "normal" || k == "help"
    || k == "vars" || k == "clear" || k == "save" || k == "load"

private def isReservedFun (k : String) : Bool :=
  k == "sin" || k == "cos" || k == "tan" || k == "exp"
    || k == "ln" || k == "log" || k == "sqrt"

private def splitKeyword (s : String) : Option String × Option String :=
  let parts := s.splitOn " " |>.filter (fun p => p ≠ "")
  match parts with
  | [] => (none, none)
  | k :: rest =>
    let kl := k.toLower
    if isKeyword kl then
      if rest.isEmpty then (some kl, none)
      else (some kl, some (" ".intercalate rest))
    else
      (none, none)

private def splitTopComma (s : String) : Option (String × String) :=
  let cs := s.toList
  let rec go (depth : Nat) (i : Nat) (last : Option Nat) : Option Nat :=
    if i < cs.length then
      match cs[i]! with
      | '(' => go (depth + 1) (i + 1) last
      | ')' => go (if depth = 0 then 0 else depth - 1) (i + 1) last
      | ',' =>
        if depth == 0 then go depth (i + 1) (some i)
        else go depth (i + 1) last
      | _ => go depth (i + 1) last
    else last
  match go 0 0 none with
  | none => none
  | some i =>
    let left := charsToString (cs.take i)
    let right := charsToString (cs.drop (i + 1))
    some (strTrim left, strTrim right)

private def isIdentString (v : String) : Bool :=
  match v.toList with
  | [] => false
  | c :: rest => isAlpha c && rest.all isIdentCont

private def trailingVar (s : String) : Option (String × String) :=
  let parts := s.splitOn " " |>.filter (fun p => p ≠ "")
  match parts.reverse with
  | v :: rest =>
    if rest.isEmpty then none
    else if isIdentString v && !isReservedFun v.toLower then
      some (" ".intercalate rest.reverse, v)
    else none
  | [] => none

private def parseVarName (s : String) (env : Env := {}) : Except String String := do
  let e ← parse s env
  asVarName e

private def parseExprAndOptionalVar (s : String) (env : Env := {}) : Except String (Expr × String) := do
  let s := strTrim s
  if let some (left, right) := splitTopComma s then
    let e ← parse left env
    let v ← parseVarName right env
    pure (e, v)
  else
    match trailingVar s with
    | some (left, v) =>
      let e ← parse left env
      pure (e, v)
    | none =>
      let e ← parse s env
      pure (e, "x")

/-- Split `name := rhs` at top-level `:=` (paren/bracket depth 0). -/
partial def splitAssign (s : String) : Option (String × String) :=
  let cs := s.toList.toArray
  let rec go (i : Nat) (depth : Nat) : Option Nat :=
    if i + 1 < cs.size then
      let c := cs[i]!
      let d :=
        match c with
        | '(' | '[' => depth + 1
        | ')' | ']' => if depth = 0 then 0 else depth - 1
        | _ => depth
      if depth == 0 && c == ':' && cs[i+1]! == '=' then some i
      else go (i + 1) d
    else none
  match go 0 0 with
  | none => none
  | some i =>
    let left := strTrim (charsToString (cs.toList.take i))
    let right := strTrim (charsToString (cs.toList.drop (i + 2)))
    if left.isEmpty || right.isEmpty then none
    else some (left, right)

/--
  Split a line into statements on top-level `;`
  (does not split inside `()` or `[]`, so matrix `[1,2;3,4]` is safe).
-/
partial def splitStatements (s : String) : List String :=
  let cs := s.toList.toArray
  Id.run do
    let mut parts : List String := []
    let mut start : Nat := 0
    let mut depth : Nat := 0
    let mut i : Nat := 0
    while i < cs.size do
      let c := cs[i]!
      match c with
      | '(' | '[' => depth := depth + 1
      | ')' | ']' => depth := if depth = 0 then 0 else depth - 1
      | ';' =>
        if depth == 0 then
          let part := strTrim (charsToString (cs.toList.drop start |>.take (i - start)))
          if !part.isEmpty then parts := parts ++ [part]
          start := i + 1
      | _ => pure ()
      i := i + 1
    let tail := strTrim (charsToString (cs.toList.drop start))
    if !tail.isEmpty then parts := parts ++ [tail]
    pure parts

/--
  Parse a calculator command line.

  Supports assignment (`name := expr`), `vars`, `clear`, calculus commands,
  and bare expressions.
-/
def parseCommand (input : String) (env : Env := {}) : Except String Command := do
  let trimmed := strTrim input
  if trimmed.isEmpty then
    throw "empty input"
  let lower := trimmed.toLower
  if lower == "help" || lower == "?" then
    pure .help
  else if lower == "vars" || lower == "bindings" then
    pure .vars
  else if lower == "clear" then
    pure .clearAll
  else if lower.startsWith "clear " then
    let name := strTrim (charsToString (trimmed.toList.drop 6))
    if name.isEmpty then pure .clearAll
    else if isBindingName name then pure (.clearOne name)
    else throw s!"clear: invalid name '{name}'"
  else if lower.startsWith "save " then
    let path := strTrim (charsToString (trimmed.toList.drop 5))
    if path.isEmpty then throw "save: missing file path"
    else pure (.save path)
  else if lower.startsWith "load " then
    let path := strTrim (charsToString (trimmed.toList.drop 5))
    if path.isEmpty then throw "load: missing file path"
    else pure (.load path)
  else if let some (lhs, rhs) := splitAssign trimmed then
    if !isBindingName lhs then
      throw s!"invalid assignment target '{lhs}'"
    let e ← parse rhs env
    pure (.assign lhs e)
  else
    let (kw, rest?) := splitKeyword trimmed
    match kw, rest? with
    | some "diff", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest env
      pure (.diff e v)
    | some "d", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest env
      pure (.diff e v)
    | some "int", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest env
      pure (.integrate e v)
    | some "integrate", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest env
      pure (.integrate e v)
    | some "simplify", some rest =>
      let e ← parse rest env
      pure (.simplify e)
    | some "expand", some rest =>
      let e ← parse rest env
      pure (.expand e)
    | some "cancel", some rest =>
      let e ← parse rest env
      pure (.cancel e)
    | some "together", some rest =>
      let e ← parse rest env
      pure (.together e)
    | some "nf", some rest | some "normal", some rest =>
      let e ← parse rest env
      pure (.normal e)
    | some "help", _ => pure .help
    | some "vars", _ => pure .vars
    | some "clear", none => pure .clearAll
    | some "clear", some rest =>
      let name := strTrim rest
      if name.isEmpty then pure .clearAll
      else if isBindingName name then pure (.clearOne name)
      else throw s!"clear: invalid name '{name}'"
    | some "save", some path =>
      let path := strTrim path
      if path.isEmpty then throw "save: missing file path"
      else pure (.save path)
    | some "load", some path =>
      let path := strTrim path
      if path.isEmpty then throw "load: missing file path"
      else pure (.load path)
    | some "save", none | some "load", none =>
      throw s!"command '{kw.getD "?"}' needs a file path"
    | some kw, none =>
      throw s!"command '{kw}' needs an expression"
    | _, _ =>
      let e ← parse trimmed env
      pure (.expr e)

/-- Pretty help text for the CLI. -/
def helpText : String :=
  "Taschenrechner — expression language\n\
  \n\
  Expressions:\n\
    numbers     0, 42, -3, 1.5, 0.25  (decimals → exact rationals)\n\
    variables   x, y, theta\n\
    ops         +  -  *  /  ^  ·  =  <  <=  >  >=   and juxtaposition (2x, sin(x)cos(x))\n\
    equations   x^2 = 4   inside solve: solve(x^2=4, x)\n\
    inequalities  solve(x^2-1>0) → (-∞,-1)∪(1,∞);  systems → x=…, y=…\n\
    functions   sin cos tan exp ln log sqrt atan re im conj abs\n\
    complex     i  (or I);  2+3*i;  euler(exp(i*x)) → cos+i·sin\n\
    matrices    [1, 2; 3, 4]  or  matrix(1, 2; 3, 4)\n\
                det inv transpose/tp trace/tr rref rank nullity\n\
                nullspace/null/ker  solve(A,b)  (general soln uses t1,t2,…)\n\
                charpoly(A)  eigvals/eigen/eig(A)  eigenspace(A,λ)\n\
                diagonalize(A)→[P,D]  modal(A)  diagform(A)  expm(A)\n\
                eye zeros ones; A*B product, c*A scalar, A^n (n≥0)\n\
    algebra     factor(e)  roots(e)  solve(f[,x])  solve(lhs=rhs,x)\n\
                solve(eq1,eq2,…) → x=…,y=…;  solve(a>b) → intervals\n\
                collect(e)  coeff(e,n)  apart(e)/pf(e)  (partial fractions)\n\
    CAS forms   diff(e)  diff(e, v)  int(e)  int(e, v)\n\
                int(f, a, b)  int(f, x, a, b)   definite (FTC)\n\
                taylor(f, n)  taylor(f, x, a, n)  maclaurin/series(f, n)\n\
                laurent(f, n)  laurent(f, a, n)  seriesadd/seriesmul(f,g,n)\n\
                limit(e, a)  limit(e, x, a[, side])  limleft/limright\n\
                poleorder(e, a)  classify(e, a)   (side: 1/right or -1/left)\n\
                sum(expr, k, lo, hi)  dsolve(eq)  (y'/yp; y''/ypp; C/C1/C2)\n\
                dsolve(y''+y=0)  2nd-order const-coeff;  dsolve(A)  Y'=A Y via expm\n\
                dsolve(eq, x0, y0)  dsolve(eq, x0, y0, yp0)  ICs;  dsolve(A, Y0)\n\
                simplify(e)  expand(e)  cancel(e)  together(e)\n\
                nf(e)/normal(e)  euler(e)\n\
                subst(e, v, a)  eval(e)  eval(e, v, a)  at(e, v, a)\n\
                N(e)  N(e, digits)  numeric(e)  — float approx, default 6 digits\n\
  \n\
  Commands:\n\
    <expr>\n\
    name := <expr>          bind a session variable\n\
    ans                     last result (auto-updated)\n\
    stmt; stmt; ...         multiple statements per line\n\
    vars                    list bindings\n\
    clear [name]            clear all or one binding\n\
    save <file>             write session bindings to file\n\
    load <file>             restore session from file\n\
    diff <expr> [var]       (default var: x)\n\
    int  <expr> [var]\n\
    simplify <expr>\n\
    expand <expr>\n\
    cancel <expr>\n\
    together <expr>\n\
    nf / normal <expr>\n\
    help\n\
  \n\
  Examples:\n\
    x^2 + 3*x + 1\n\
    A := [1, 2; 3, 4]; det(A)\n\
    b := [5; 11]; solve(A, b)\n\
    solve(x+y=1, x-y=3)\n\
    solve(x^2-1>0)\n\
    ans\n\
    save session.tr\n\
    load session.tr\n\
    vars\n\
    clear A\n\
    diff sin(x^2)\n\
    int x*exp(x)"

end Taschenrechner.Parse
