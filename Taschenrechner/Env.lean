/-
  Session environment: named bindings for the REPL and command runner.

  Bindings store fully substituted, simplified expressions so evaluation is
  order-independent for acyclic environments.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify

namespace Taschenrechner

open Expr

/-- Variable environment: ordered list of (name, value); later entries shadow earlier. -/
structure Env where
  bindings : Array (String × Expr) := #[]
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
  { bindings := env.bindings.filter (fun (n, _) => n != name) }

/-- Set/replace binding. -/
def set (env : Env) (name : String) (value : Expr) : Env :=
  { bindings := (env.erase name).bindings.push (name, value) }

def clear (_env : Env) : Env := empty

/-- Names currently bound (alphabetical). -/
def names (env : Env) : List String :=
  env.bindings.toList.map (·.1) |>.eraseDups |>.mergeSort (· < ·)

/-- Pretty listing for `vars`. -/
def format (env : Env) : String :=
  if env.isEmpty then "(no bindings)"
  else
    let lines :=
      env.names.filterMap fun n =>
        match env.get? n with
        | some e => some s!"  {n} := {e}"
        | none => none
    String.intercalate "\n" lines

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
  | exp a => exp (substEnv env a)
  | ln a => ln (substEnv env a)
  | atan a => atan (substEnv env a)
  | re a => re (substEnv env a)
  | im a => im (substEnv env a)
  | conj a => conj (substEnv env a)
  | mat rows => mat (rows.map fun row => row.map (substEnv env))

/-- Names that must not be used as binding targets. -/
def isForbiddenBinding (name : String) : Bool :=
  let n := name.toLower
  n == "i" || n == "help" || n == "vars" || n == "clear" || n == "quit"
    || n == "exit" || n == "diff" || n == "int" || n == "integrate"
    || n == "simplify" || n == "expand" || n == "euler"

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
  let val := Expr.simplify (substEnv env rhs)
  if Expr.dependsOn val name then
    throw s!"recursive binding: {name} depends on itself"
  let env' := env.set name val
  pure (env', val)

end Taschenrechner
