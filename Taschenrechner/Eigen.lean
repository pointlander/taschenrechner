/-
  Characteristic polynomial, eigenvalues, and eigenspaces over Expr.

  * `charpoly A` = det(t I − A) (monic in `t` by default)
  * `eigenvalues A` — roots of the char poly (rational + quadratic formula)
  * `eigenspace A λ` — nullspace of (A − λ I)
-/
import Taschenrechner.Simplify
import Taschenrechner.Matrix
import Taschenrechner.LinAlg
import Taschenrechner.Solve
import Taschenrechner.Normal

namespace Taschenrechner.Mat

open Expr
open Taschenrechner

/-- Default indeterminate for the characteristic polynomial. -/
def charVar : String := "t"

/-- `λ·I − A` (same shape as square `A`). -/
def charMatrix (A : Array (Array Expr)) (lam : Expr) : Option (Array (Array Expr)) :=
  let n := nrows A
  if n == 0 || n != ncols A then none
  else sub (scale lam (eye n)) A

/-- `A − λ·I`. -/
def shiftByEigenvalue (A : Array (Array Expr)) (lam : Expr) : Option (Array (Array Expr)) :=
  let n := nrows A
  if n == 0 || n != ncols A then none
  else sub A (scale lam (eye n))

/--
  Characteristic polynomial `det(t I − A)` as an expression in free variable `v`
  (default `"t"`). Collected into canonical poly form when possible.
-/
def charpoly (A : Array (Array Expr)) (v : String := charVar) : Option Expr :=
  match charMatrix A (var v) with
  | none => none
  | some M =>
    match det M with
    | none => none
    | some d =>
      let d := simplify d
      match collectIn d v with
      | some c => some c
      | none => some (Expr.normalForm d v)

/--
  Eigenvalues of square `A`: roots of `charpoly` in `"t"`.
  Returns `none` if `A` is not square. May be a partial list if the char poly
  has irreducible factors of degree ≥ 3.
-/
def eigenvalues (A : Array (Array Expr)) : Option (List Expr) :=
  match charpoly A charVar with
  | none => none
  | some p =>
    match solveScalar p charVar with
    | .solutions rs => some rs
    | .all => some []
    | .empty => some []
    | .unsupported _ => some (roots p charVar)

/-- Eigenvalues as a 1×k row matrix expression. -/
def eigenvaluesMat (A : Array (Array Expr)) : Option (Array (Array Expr)) :=
  match eigenvalues A with
  | none => none
  | some rs => some #[rs.toArray]

/--
  Eigenspace for eigenvalue `lam`: nullspace of `(A − lam·I)`.
  Columns of the returned matrix form a basis (may be empty if `lam` is not
  an eigenvalue or geometric multiplicity is 0 under exact arithmetic).
-/
def eigenspace (A : Array (Array Expr)) (lam : Expr) : Option (Array (Array Expr)) :=
  match shiftByEigenvalue A (simplify lam) with
  | none => none
  | some M =>
    let M := map M simp
    some (nullspace M)

/--
  Factor the characteristic polynomial over ℚ when possible
  (product of linear/irreducible factors in `v`).
-/
def charpolyFactor (A : Array (Array Expr)) (v : String := charVar) : Option Expr :=
  match charpoly A v with
  | none => none
  | some p => some (factor p v)

end Taschenrechner.Mat
