/-
  Substitution and exact evaluation.

  * `subst` / `substMany` — free-variable replacement (defined on `Expr`)
  * `eval?` — evaluate a ground expression in ℚ(i)
  * `evalAt` — substitute then simplify (symbolic)
  * `evalAt?` — substitute a constant and evaluate in ℚ(i)
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Complex

namespace Taschenrechner

open Expr

/-- Re-export for a single import surface. -/
def subst (e : Expr) (v : String) (val : Expr) : Expr := Expr.subst e v val
def substMany (e : Expr) (σ : List (String × Expr)) : Expr := Expr.substMany e σ

/-- Exact evaluation of a constant (ground) expression over ℚ(i). -/
def eval? (e : Expr) : Option CplxConst :=
  evalCplx? (simplify e)

/-- Substitute `v ↦ val` and simplify (always succeeds; may leave free vars). -/
def evalAt (e : Expr) (v : String) (val : Expr) : Expr :=
  simplify (Expr.subst e v val)

/-- Substitute several variables then simplify. -/
def evalAtMany (e : Expr) (σ : List (String × Expr)) : Expr :=
  simplify (Expr.substMany e σ)

/--
  Substitute `v ↦ c` (constant) and evaluate to `CplxConst` when the result
  is ground. Returns `none` if free vars or non-elementary constants remain.
-/
def evalAt? (e : Expr) (v : String) (c : CplxConst) : Option CplxConst :=
  eval? (Expr.subst e v (const c))

/-- Evaluate with a list of constant bindings. -/
def evalWith? (e : Expr) (σ : List (String × CplxConst)) : Option CplxConst :=
  let e := σ.foldl (fun acc pair => Expr.subst acc pair.1 (const pair.2)) e
  eval? e

/--
  Evaluate if ground; otherwise substitute and simplify.
  Useful for `eval(e)` / `eval(e, x, a)` in the parser.
-/
def evalOrSimplify (e : Expr) : Expr :=
  match eval? e with
  | some c => const c
  | none => simplify e

def evalAtOrSimplify (e : Expr) (v : String) (val : Expr) : Expr :=
  match eval? (Expr.subst e v val) with
  | some c => const c
  | none => simplify (Expr.subst e v val)

end Taschenrechner
