/-
  Session environment: named bindings for the REPL and command runner.

  Bindings store fully substituted, simplified expressions so evaluation is
  order-independent for acyclic environments.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify

namespace Taschenrechner

open Expr

/-- Sign / vanishing assumption on a real variable. -/
inductive SignPred where
  | pos      -- x > 0
  | nonneg   -- x ≥ 0
  | neg      -- x < 0
  | nonpos   -- x ≤ 0
  | nonzero  -- x ≠ 0
  | integer  -- x ∈ ℤ
  deriving Repr, BEq, Inhabited, DecidableEq

namespace SignPred

def toString : SignPred → String
  | pos => "> 0"
  | nonneg => "≥ 0"
  | neg => "< 0"
  | nonpos => "≤ 0"
  | nonzero => "≠ 0"
  | integer => "∈ ℤ"

def impliesPos : SignPred → Bool
  | pos => true
  | _ => false

def impliesNonneg : SignPred → Bool
  | pos | nonneg => true
  | _ => false

def impliesNeg : SignPred → Bool
  | neg => true
  | _ => false

def impliesNonpos : SignPred → Bool
  | neg | nonpos => true
  | _ => false

def impliesNonzero : SignPred → Bool
  | pos | neg | nonzero => true
  | _ => false

/-- Keyword used in `assume(x, pos)` and session files. -/
def toTag : SignPred → String
  | pos => "pos"
  | nonneg => "nonneg"
  | neg => "neg"
  | nonpos => "nonpos"
  | nonzero => "nonzero"
  | integer => "int"

def ofTag? (s : String) : Option SignPred :=
  match s.toLower with
  | "pos" | "positive" | "plus" => some pos
  | "nonneg" | "nonnegative" | "nn" => some nonneg
  | "neg" | "negative" | "minus" => some neg
  | "nonpos" | "nonpositive" | "np" => some nonpos
  | "nonzero" | "nz" | "ne0" => some nonzero
  | "int" | "integer" | "z" | "ℤ" => some integer
  | _ => none

end SignPred

/-- Variable environment: ordered list of (name, value); later entries shadow earlier. -/
structure Env where
  bindings : Array (String × Expr) := #[]
  /-- Sign assumptions on free variables (`assume`). -/
  assumes : Array (String × SignPred) := #[]
  deriving Repr, Inhabited

namespace Env

def empty : Env := {}

def isEmpty (env : Env) : Bool := env.bindings.isEmpty

def size (env : Env) : Nat := env.bindings.size

/-- Lookup binding (most recent wins). -/
def get? (env : Env) (name : String) : Option Expr :=
  Id.run do
    let mut i := env.bindings.size
    while i > 0 do
      i := i - 1
      let (n, e) := env.bindings[i]!
      if n == name then return some e
    pure none

/-- Remove all bindings of `name`. -/
def erase (env : Env) (name : String) : Env :=
  { env with bindings := env.bindings.filter (fun (n, _) => n != name) }

/-- Set/replace binding. -/
def set (env : Env) (name : String) (value : Expr) : Env :=
  { env with bindings := (env.erase name).bindings.push (name, value) }

/-- Lookup a sign assumption. -/
def getAssume? (env : Env) (name : String) : Option SignPred :=
  Id.run do
    let mut i := env.assumes.size
    while i > 0 do
      i := i - 1
      let (n, p) := env.assumes[i]!
      if n == name then return some p
    pure none

/-- Remove assumption on `name`. -/
def eraseAssume (env : Env) (name : String) : Env :=
  { env with assumes := env.assumes.filter (fun (n, _) => n != name) }

/-- Set/replace a sign assumption. -/
def setAssume (env : Env) (name : String) (p : SignPred) : Env :=
  { env with assumes := (env.eraseAssume name).assumes.push (name, p) }

def clearAssumes (env : Env) : Env :=
  { env with assumes := #[] }

def assumeNames (env : Env) : List String :=
  env.assumes.toList.map (·.1) |>.eraseDups |>.mergeSort (· < ·)

def clear (_env : Env) : Env := empty

/-- Names currently bound (alphabetical). -/
def names (env : Env) : List String :=
  env.bindings.toList.map (·.1) |>.eraseDups |>.mergeSort (· < ·)

/-- Pretty listing for `vars`. -/
def format (env : Env) : String :=
  let binds :=
    if env.isEmpty then []
    else
      env.names.filterMap fun n =>
        match env.get? n with
        | some e => some s!"  {n} := {e}"
        | none => none
  let asms :=
    env.assumeNames.filterMap fun n =>
      match env.getAssume? n with
      | some p => some s!"  {n} {SignPred.toString p}"
      | none => none
  match binds, asms with
  | [], [] => "(no bindings)"
  | bs, [] => String.intercalate "\n" bs
  | [], as => "assumes:\n" ++ String.intercalate "\n" as
  | bs, as => String.intercalate "\n" bs ++ "\nassumes:\n" ++ String.intercalate "\n" as

/-- Update the special `ans` binding (last result). -/
def setAns (env : Env) (value : Expr) : Env :=
  env.set "ans" value

/--
  Serialize environment to a reloadable session file body.
  Format: lines `name := <expr>` (printable form), `#` comments allowed on load.
-/
def toSession (env : Env) : String :=
  let header := "# taschenrechner session v1\n"
  let lines :=
    env.names.filterMap fun n =>
      match env.get? n with
      | some e => some s!"{n} := {e}"
      | none => none
  let asms :=
    env.assumeNames.filterMap fun n =>
      match env.getAssume? n with
      | some p => some s!"assume({n}, {p.toTag})"
      | none => none
  header ++ String.intercalate "\n" (lines ++ asms) ++ "\n"

end Env

/--
  Substitute environment bindings into an expression.
  Bound names are replaced by their stored values (already closed w.r.t. env).
-/
partial def substEnv (env : Env) (e : Expr) : Expr :=
  match e with
  | const c => const c
  | var name =>
    match env.get? name with
    | some val => val
    | none => var name
  | add a b => add (substEnv env a) (substEnv env b)
  | mul a b => mul (substEnv env a) (substEnv env b)
  | pow a b => pow (substEnv env a) (substEnv env b)
  | sin a => sin (substEnv env a)
  | cos a => cos (substEnv env a)
  | tan a => tan (substEnv env a)
  | sinh a => sinh (substEnv env a)
  | cosh a => cosh (substEnv env a)
  | tanh a => tanh (substEnv env a)
  | exp a => exp (substEnv env a)
  | ln a => ln (substEnv env a)
  | atan a => atan (substEnv env a)
  | asin a => asin (substEnv env a)
  | acos a => acos (substEnv env a)
  | sec a => sec (substEnv env a)
  | csc a => csc (substEnv env a)
  | cot a => cot (substEnv env a)
  | factorial a => factorial (substEnv env a)
  | gamma a => gamma (substEnv env a)
  | floor a => floor (substEnv env a)
  | Expr.ite c t e => Expr.ite (substEnv env c) (substEnv env t) (substEnv env e)
  | abs a => abs (substEnv env a)
  | re a => re (substEnv env a)
  | im a => im (substEnv env a)
  | conj a => conj (substEnv env a)
  | eq a b => eq (substEnv env a) (substEnv env b)
  | lt a b => lt (substEnv env a) (substEnv env b)
  | le a b => le (substEnv env a) (substEnv env b)
  | mat rows => mat (rows.map fun row => row.map (substEnv env))

/-- True when `e` is an integer constant or an assumed integer expression. -/
partial def isIntExpr (env : Env) : Expr → Bool
  | const c =>
    match CplxConst.toRat? c with
    | some q => q.den == 1
    | none => false
  | var v => env.getAssume? v == some .integer
  | add a b | mul a b => isIntExpr env a && isIntExpr env b
  | pow a (const c) =>
    match CplxConst.toRat? c with
    | some q => q.den == 1 && q.num ≥ 0 && isIntExpr env a
    | none => false
  | e =>
    match e with
    | mul (const c) u =>
      match CplxConst.toRat? c with
      | some q => q.den == 1 && isIntExpr env u
      | none => false
    | _ => false

/-- If `e = n·π` with integer `n`, return `n`. -/
def asIntPi? (env : Env) : Expr → Option Expr
  | var v => if Expr.isPiName v then some one else none
  | mul a b =>
    if Expr.isPiName (match a with | var v => v | _ => "") && isIntExpr env b then
      some b
    else if Expr.isPiName (match b with | var v => v | _ => "") && isIntExpr env a then
      some a
    else
      match asRatPi? (mul a b) with
      | some q =>
        if q.den == 1 then some (ofInt q.num) else none
      | none => none
  | e =>
    match asRatPi? e with
    | some q => if q.den == 1 then some (ofInt q.num) else none
    | none => none

/-- Inferred sign of a ground constant or assumed variable. -/
def signOf (env : Env) : Expr → Option SignPred
  | var v => env.getAssume? v
  | const c =>
    match CplxConst.toRat? c with
    | some q =>
      if q.num > 0 then some .pos
      else if q.num < 0 then some .neg
      else none
    | none => none
  | abs _ => some .nonneg
  | _ => none

private def isRat (e : Expr) (q : RatConst) : Bool :=
  match e with
  | const c =>
    match CplxConst.toRat? c with
    | some r => r == q
    | none => false
  | _ => false

/--
  Apply session sign assumptions:
  * `√(v²)` → `v` / `-v` / `|v|` according to the sign of `v`
  * `|v|` → `v` or `-v` when the sign is known
  * `ln(v^n)` → `n·ln(v)` when `v > 0`
-/
partial def applyAssumes (env : Env) : Expr → Expr
  | const c => const c
  | var v => var v
  | add a b => add (applyAssumes env a) (applyAssumes env b)
  | mul a b => mul (applyAssumes env a) (applyAssumes env b)
  | pow base ex =>
    let base := applyAssumes env base
    let ex := applyAssumes env ex
    if isRat ex ⟨1, 2⟩ then
      match base with
      | pow u e2 =>
        if isRat e2 ⟨2, 1⟩ then
          match signOf env u with
          | some p =>
            if p.impliesNonneg then u
            else if p.impliesNonpos then neg u
            else abs u
          | none => abs u
        else pow base ex
      | _ => pow base ex
    else pow base ex
  | sin a =>
    let a := applyAssumes env a
    match asIntPi? env a with
    | some _ => zero  -- sin(nπ) = 0
    | none => sin a
  | cos a =>
    let a := applyAssumes env a
    match asIntPi? env a with
    | some n => pow (negOne) n  -- cos(nπ) = (−1)ⁿ
    | none => cos a
  | tan a =>
    let a := applyAssumes env a
    match asIntPi? env a with
    | some _ => zero
    | none => tan a
  | sinh a => sinh (applyAssumes env a)
  | cosh a => cosh (applyAssumes env a)
  | tanh a => tanh (applyAssumes env a)
  | exp a => exp (applyAssumes env a)
  | ln a =>
    let a := applyAssumes env a
    match a with
    | pow u e =>
      match signOf env u with
      | some p =>
        if p.impliesPos then simplify (mul e (ln u)) else ln a
      | none => ln a
    | abs u =>
      match signOf env u with
      | some p =>
        if p.impliesPos then ln u else ln a
      | none => ln a
    | _ => ln a
  | atan a => atan (applyAssumes env a)
  | asin a => asin (applyAssumes env a)
  | acos a => acos (applyAssumes env a)
  | sec a => sec (applyAssumes env a)
  | csc a => csc (applyAssumes env a)
  | cot a => cot (applyAssumes env a)
  | factorial a => factorial (applyAssumes env a)
  | gamma a => gamma (applyAssumes env a)
  | floor a => floor (applyAssumes env a)
  | Expr.ite c t e => Expr.ite (applyAssumes env c) (applyAssumes env t) (applyAssumes env e)
  | abs a =>
    let a := applyAssumes env a
    match signOf env a with
    | some p =>
      if p.impliesNonneg then a
      else if p.impliesNonpos then neg a
      else abs a
    | none => abs a
  | re a => re (applyAssumes env a)
  | im a => im (applyAssumes env a)
  | conj a => conj (applyAssumes env a)
  | eq a b => eq (applyAssumes env a) (applyAssumes env b)
  | lt a b => lt (applyAssumes env a) (applyAssumes env b)
  | le a b => le (applyAssumes env a) (applyAssumes env b)
  | mat rows => mat (rows.map fun row => row.map (applyAssumes env))

/-- `simplify` after substituting bindings and applying assumes. -/
def evalWithEnv (env : Env) (e : Expr) : Expr :=
  applyAssumes env (simplify (substEnv env e))

/-- Marker used to encode `assume` / `forget` for the parser → CLI path. -/
def assumeMarker : String := "__assume__"
def forgetMarker : String := "__forget__"

inductive AssumeReq where
  | set : String → SignPred → AssumeReq
  | show : AssumeReq
  | forget : Option String → AssumeReq
  deriving Repr

def assumeReqToExpr : AssumeReq → Expr
  | .set v p => mat #[#[var assumeMarker, var v, var p.toTag]]
  | .show => mat #[#[var assumeMarker]]
  | .forget none => mat #[#[var forgetMarker]]
  | .forget (some v) => mat #[#[var forgetMarker, var v]]

def asAssumeReq? : Expr → Option AssumeReq
  | mat rows =>
    if rows.size == 1 && rows[0]!.size ≥ 1 then
      match rows[0]![0]! with
      | var m =>
        if m == assumeMarker then
          if rows[0]!.size == 1 then some .show
          else if rows[0]!.size == 3 then
            match rows[0]![1]!, rows[0]![2]! with
            | var v, var tag =>
              match SignPred.ofTag? tag with
              | some p => some (.set v p)
              | none => none
            | _, _ => none
          else none
        else if m == forgetMarker then
          if rows[0]!.size == 1 then some (.forget none)
          else if rows[0]!.size == 2 then
            match rows[0]![1]! with
            | var v => some (.forget (some v))
            | _ => none
          else none
        else none
      | _ => none
    else none
  | _ => none

/-- Turn a comparison with 0 into a sign predicate. -/
def signFromRel? (e : Expr) : Option (String × SignPred) :=
  let e := simplify e
  match e with
  | lt a b =>
    match a, b with
    | var v, const c =>
      match CplxConst.toRat? c with
      | some q => if q.isZero then some (v, .neg) else none
      | none => none
    | const c, var v =>
      match CplxConst.toRat? c with
      | some q => if q.isZero then some (v, .pos) else none
      | none => none
    | _, _ => none
  | le a b =>
    match a, b with
    | var v, const c =>
      match CplxConst.toRat? c with
      | some q => if q.isZero then some (v, .nonpos) else none
      | none => none
    | const c, var v =>
      match CplxConst.toRat? c with
      | some q => if q.isZero then some (v, .nonneg) else none
      | none => none
    | _, _ => none
  | _ => none

/-- Names that must not be used as binding targets. -/
def isForbiddenBinding (name : String) : Bool :=
  let n := name.toLower
  -- `ans` is allowed (user may assign; REPL also auto-updates it)
  n == "i" || n == "help" || n == "vars" || n == "clear" || n == "quit"
    || n == "exit" || n == "diff" || n == "int" || n == "integrate"
    || n == "simplify" || n == "expand" || n == "euler"
    || n == "save" || n == "load" || n == "assume" || n == "forget"
    || n == "unassume" || n == "assumptions" || n == "pi" || name == "π"

/-- Valid identifier for a binding name. -/
def isBindingName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: rest =>
    (('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_')
      && rest.all fun d =>
        ('a' ≤ d && d ≤ 'z') || ('A' ≤ d && d ≤ 'Z') || ('0' ≤ d && d ≤ '9') || d == '_'

/--
  Assign `name := rhs` under `env`.
  RHS is environment-substituted and simplified; rejects recursive/forbidden names.
-/
def envAssign (env : Env) (name : String) (rhs : Expr) : Except String (Env × Expr) := do
  if !isBindingName name then
    throw s!"invalid binding name '{name}'"
  if isForbiddenBinding name then
    throw s!"cannot bind reserved name '{name}'"
  let val := evalWithEnv env rhs
  if Expr.dependsOn val name then
    throw s!"recursive binding: {name} depends on itself"
  let env' := env.set name val
  pure (env', val)

end Taschenrechner
