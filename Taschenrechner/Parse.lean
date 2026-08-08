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
import Taschenrechner.Diff
import Taschenrechner.Integrate

namespace Taschenrechner.Parse

open Taschenrechner
open Taschenrechner.Expr

/-! ### Tokens -/

inductive Token where
  | num   : Int → Token
  | ident : String → Token
  | plus | minus | star | slash | caret | middot
  | lparen | rparen | comma
  | eof
  deriving Repr, DecidableEq, Inhabited

def Token.toString : Token → String
  | .num n => s!"{n}"
  | .ident s => s
  | .plus => "+"
  | .minus => "-"
  | .star => "*"
  | .slash => "/"
  | .caret => "^"
  | .middot => "·"
  | .lparen => "("
  | .rparen => ")"
  | .comma => ","
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
    else if isDigit c then
      let start := i
      i := i + 1
      while i < len && isDigit cs[i]! do
        i := i + 1
      if i < len && cs[i]! == '.' then
        throw s!"decimal literals are not supported (use fractions like 1/2); at position {start}"
      let digits := charsToString (cs.extract start i).toList
      match digits.toInt? with
      | some n => out := out.push (.num n)
      | none => throw s!"invalid number '{digits}'"
    else if isAlpha c then
      let start := i
      i := i + 1
      while i < len && isIdentCont cs[i]! do
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
      | '(' => out := out.push .lparen; i := i + 1
      | ')' => out := out.push .rparen; i := i + 1
      | ',' => out := out.push .comma; i := i + 1
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
  | .num _ | .ident _ | .lparen => true
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
  | "simplify", [e] => pure (simplify e)
  | "expand", [e] => pure (expand e)
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
  | "integrate", [e] => integrateCall e "x"
  | "integrate", [e, v] => do
      let v ← asVarName v
      integrateCall e v
  | "sin", _ | "cos", _ | "tan", _ | "exp", _ | "ln", _ | "log", _ | "sqrt", _
  | "atan", _ | "arctan", _
  | "simplify", _ | "expand", _ =>
      throw s!"{name} expects 1 argument, got {args.length}"
  | "diff", _ | "d", _ | "int", _ | "integrate", _ =>
      throw s!"{name} expects 1 or 2 arguments, got {args.length}"
  | _, _ =>
      throw s!"unknown function '{name}'"

/-- Known callables that consume `(...)`; bare vars juxtapose: `x(x+1)` = `x*(x+1)`. -/
def isBuiltinName (name : String) : Bool :=
  let n := name.toLower
  n == "sin" || n == "cos" || n == "tan" || n == "exp" || n == "ln" || n == "log"
    || n == "sqrt" || n == "atan" || n == "arctan" || n == "simplify" || n == "expand"
    || n == "diff" || n == "d" || n == "int" || n == "integrate"

/-! ### Recursive-descent parsing -/

mutual

partial def parseExpr (p : Parser) : Except String (Expr × Parser) :=
  parseSum p

partial def parseSum (p : Parser) : Except String (Expr × Parser) := do
  let (lhs, p) ← parseProduct p
  go lhs p
where
  go (lhs : Expr) (p : Parser) : Except String (Expr × Parser) := do
    match p.peek with
    | .plus =>
      let (rhs, p) ← parseProduct p.advance
      go (Expr.add lhs rhs) p
    | .minus =>
      let (rhs, p) ← parseProduct p.advance
      go (Expr.sub lhs rhs) p
    | _ => pure (lhs, p)

partial def parseProduct (p : Parser) : Except String (Expr × Parser) := do
  let (lhs, p) ← parseUnary p
  go lhs p
where
  go (lhs : Expr) (p : Parser) : Except String (Expr × Parser) := do
    match p.peek with
    | .star | .middot =>
      let (rhs, p) ← parseUnary p.advance
      go (Expr.mul lhs rhs) p
    | .slash =>
      let (rhs, p) ← parseUnary p.advance
      go (Expr.div lhs rhs) p
    | t =>
      if t.startsAtom then
        let (rhs, p) ← parseUnary p
        go (Expr.mul lhs rhs) p
      else
        pure (lhs, p)

/-- Unary binds looser than `^`, so `-x^2` = `-(x^2)`. -/
partial def parseUnary (p : Parser) : Except String (Expr × Parser) := do
  match p.peek with
  | .plus => parseUnary p.advance
  | .minus =>
    let (e, p) ← parseUnary p.advance
    pure (Expr.neg e, p)
  | _ => parsePower p

/-- Right-associative exponentiation: `a^b^c` = `a^(b^c)`. -/
partial def parsePower (p : Parser) : Except String (Expr × Parser) := do
  let (lhs, p) ← parseAtom p
  match p.peek with
  | .caret =>
    let (rhs, p) ← parseUnary p.advance
    pure (Expr.pow lhs rhs, p)
  | _ => pure (lhs, p)

partial def parseAtom (p : Parser) : Except String (Expr × Parser) := do
  match p.peek with
  | .num n => pure (Expr.ofInt n, p.advance)
  | .ident name => parseIdent name p.advance
  | .lparen =>
    let (e, p) ← parseExpr p.advance
    let p ← p.expect .rparen
    pure (e, p)
  | t => throw s!"expected number, identifier, or '(', got '{t}'"

partial def parseIdent (name : String) (p : Parser) : Except String (Expr × Parser) := do
  if p.peek == .lparen && isBuiltinName name then
    let (args, p) ← parseArgList p.advance
    let e ← applyCall name args
    pure (e, p)
  else
    pure (Expr.var name, p)

partial def parseArgList (p : Parser) : Except String (List Expr × Parser) := do
  if p.peek == .rparen then
    pure ([], p.advance)
  else
    let (e, p) ← parseExpr p
    let (rest, p) ← parseArgListCont p
    pure (e :: rest, p)

partial def parseArgListCont (p : Parser) : Except String (List Expr × Parser) := do
  match p.peek with
  | .comma =>
    let (e, p) ← parseExpr p.advance
    let (rest, p) ← parseArgListCont p
    pure (e :: rest, p)
  | .rparen => pure ([], p.advance)
  | t => throw s!"expected ',' or ')', got '{t}'"

end

/-! ### Public API -/

/-- Parse a full expression string; trailing input is an error. -/
def parse (input : String) : Except String Expr := do
  let tokens ← tokenize input
  let p : Parser := { tokens, pos := 0 }
  if p.peek == .eof then
    throw "empty expression"
  let (e, p) ← parseExpr p
  match p.peek with
  | .eof => pure (simplify e)
  | t => throw s!"unexpected token '{t}' after expression"

/-- Parse without simplifying (useful for debugging the AST). -/
def parseRaw (input : String) : Except String Expr := do
  let tokens ← tokenize input
  let p : Parser := { tokens, pos := 0 }
  if p.peek == .eof then
    throw "empty expression"
  let (e, p) ← parseExpr p
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
  | help      : Command
  deriving Repr

private def isKeyword (k : String) : Bool :=
  k == "diff" || k == "d" || k == "int" || k == "integrate"
    || k == "simplify" || k == "expand" || k == "help"

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

private def parseVarName (s : String) : Except String String := do
  let e ← parse s
  asVarName e

private def parseExprAndOptionalVar (s : String) : Except String (Expr × String) := do
  let s := strTrim s
  if let some (left, right) := splitTopComma s then
    let e ← parse left
    let v ← parseVarName right
    pure (e, v)
  else
    match trailingVar s with
    | some (left, v) =>
      let e ← parse left
      pure (e, v)
    | none =>
      let e ← parse s
      pure (e, "x")

/--
  Parse a calculator command line.

  Supported forms:
  * `<expr>`
  * `diff <expr>` / `diff <expr> <var>`
  * `int <expr>`  / `int <expr> <var>`
  * `simplify <expr>` / `expand <expr>`
  * `help`
  * or CAS calls inside expressions: `diff(sin(x^2), x)`
-/
def parseCommand (input : String) : Except String Command := do
  let trimmed := strTrim input
  if trimmed.isEmpty then
    throw "empty input"
  let lower := trimmed.toLower
  if lower == "help" || lower == "?" then
    pure .help
  else
    let (kw, rest?) := splitKeyword trimmed
    match kw, rest? with
    | some "diff", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest
      pure (.diff e v)
    | some "d", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest
      pure (.diff e v)
    | some "int", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest
      pure (.integrate e v)
    | some "integrate", some rest =>
      let (e, v) ← parseExprAndOptionalVar rest
      pure (.integrate e v)
    | some "simplify", some rest =>
      let e ← parse rest
      pure (.simplify e)
    | some "expand", some rest =>
      let e ← parse rest
      pure (.expand e)
    | some "help", _ => pure .help
    | some kw, none =>
      throw s!"command '{kw}' needs an expression"
    | _, _ =>
      let e ← parse trimmed
      pure (.expr e)

/-- Pretty help text for the CLI. -/
def helpText : String :=
  "Taschenrechner — expression language\n\
  \n\
  Expressions:\n\
    numbers     0, 42, -3\n\
    variables   x, y, theta\n\
    ops         +  -  *  /  ^  ·   and juxtaposition (2x, sin(x)cos(x))\n\
    functions   sin cos tan exp ln log sqrt\n\
    CAS forms   diff(e)  diff(e, v)  int(e)  int(e, v)\n\
                simplify(e)  expand(e)\n\
  \n\
  Commands:\n\
    <expr>\n\
    diff <expr> [var]       (default var: x)\n\
    int  <expr> [var]\n\
    simplify <expr>\n\
    expand <expr>\n\
    help\n\
  \n\
  Examples:\n\
    x^2 + 3*x + 1\n\
    diff sin(x^2)\n\
    int x*exp(x)\n\
    diff(sin(x^2), x)\n\
    int(1/x, x)"

end Taschenrechner.Parse
