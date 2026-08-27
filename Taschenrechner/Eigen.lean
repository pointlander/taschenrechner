/-
  Characteristic polynomial, eigenvalues, and eigenspaces over Expr.

  * `charpoly A` = det(t I − A) (monic in `t` by default)
  * `eigenvalues A` — roots of the char poly (rational, quadratic, cubic, quartic)
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
  has irreducible factors of degree ≥ 5.
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

/-! ### Diagonalization & matrix exponential -/

/-- Structural equality of eigenvalue expressions after simplify. -/
def eigEq (a b : Expr) : Bool :=
  simplify a == simplify b

/-- Unique eigenvalues preserving first-occurrence order. -/
def uniqueEigenvalues (rs : List Expr) : List Expr :=
  rs.foldl (fun acc lam =>
    if acc.any (fun mu => eigEq mu lam) then acc else acc ++ [lam]) []

/-- Algebraic multiplicity of `lam` in the eigenvalue list. -/
def algMultiplicity (rs : List Expr) (lam : Expr) : Nat :=
  (rs.filter (fun mu => eigEq mu lam)).length

/-- Extract column `c` as an array of length `nrows`. -/
def getColumn (M : Array (Array Expr)) (c : Nat) : Array Expr :=
  Id.run do
    let mut col : Array Expr := Array.empty
    for r in [:nrows M] do
      col := col.push (get! M r c)
    pure col

/-- Build a matrix from a list of columns (each column is an array of row entries). -/
def fromColumns (cols : List (Array Expr)) : Option (Array (Array Expr)) :=
  match cols with
  | [] => some #[]
  | c0 :: _ =>
    let n := c0.size
    if cols.any (fun c => c.size != n) then none
    else
      some <| Id.run do
        let mut rows : Array (Array Expr) := Array.empty
        for r in [:n] do
          let mut row : Array Expr := Array.empty
          for col in cols do
            row := row.push col[r]!
          rows := rows.push row
        pure rows

/-- Diagonal matrix with given diagonal entries. -/
def diagonal (entries : List Expr) : Array (Array Expr) :=
  let n := entries.length
  Id.run do
    let mut rows : Array (Array Expr) := Array.empty
    for i in [:n] do
      let mut row : Array Expr := Array.empty
      for j in [:n] do
        row := row.push (if i == j then entries[i]! else Expr.zero)
      rows := rows.push row
    pure rows

/-- Map a function over the diagonal of a square matrix (off-diagonal stay 0). -/
def mapDiagonal (D : Array (Array Expr)) (f : Expr → Expr) : Option (Array (Array Expr)) :=
  let n := nrows D
  if n == 0 || n != ncols D then none
  else
    some <| Id.run do
      let mut rows : Array (Array Expr) := Array.empty
      for i in [:n] do
        let mut row : Array Expr := Array.empty
        for j in [:n] do
          if i == j then row := row.push (f (get! D i i))
          else row := row.push Expr.zero
        rows := rows.push row
      pure rows

/-- Simplify every entry. -/
def simpMat (M : Array (Array Expr)) : Array (Array Expr) :=
  map M simp

/-- Result of attempting diagonalization. -/
inductive DiagResult where
  /-- `P⁻¹ A P = D` with `D` diagonal. -/
  | ok (P : Array (Array Expr)) (D : Array (Array Expr))
  /-- Not diagonalizable over the available eigenvalue field (defective / incomplete). -/
  | defective (msg : String)
  | error (msg : String)
  deriving Repr, Inhabited

namespace DiagResult

/-- Encode as 1×2 matrix of matrices: `[P, D]`. -/
def toExpr? : DiagResult → Except String Expr
  | .ok P D => pure (Expr.mat #[#[Expr.mat (simpMat P), Expr.mat (simpMat D)]])
  | .defective msg => throw msg
  | .error msg => throw msg

def P? : DiagResult → Option (Array (Array Expr))
  | .ok P _ => some P
  | _ => none

def D? : DiagResult → Option (Array (Array Expr))
  | .ok _ D => some D
  | _ => none

end DiagResult

/--
  Diagonalize square `A` when a full eigenbasis is available:
  collect eigenspace bases for each distinct eigenvalue; require
  total number of independent columns = n and `det P ≠ 0`.
-/
def diagonalize (A : Array (Array Expr)) : DiagResult :=
  let n := nrows A
  if n == 0 || n != ncols A then .error "diagonalize: expected square matrix"
  else
    match eigenvalues A with
    | none => .error "diagonalize: could not compute eigenvalues"
    | some rs =>
      if rs.length < n then
        .defective s!"incomplete eigenvalue list (got {rs.length}, need {n}); charpoly may not split"
      else
        let uniq := uniqueEigenvalues rs
        Id.run do
          let mut cols : List (Array Expr) := []
          let mut diagEntries : List Expr := []
          for lam in uniq do
            match eigenspace A lam with
            | none => return .error s!"eigenspace failed for lam = {lam}"
            | some N =>
              let geo := ncols N
              if geo == 0 then
                return .defective s!"no eigenvectors for eigenvalue {lam}"
              let alg := algMultiplicity rs lam
              -- take up to alg independent columns (geo should be ≤ alg)
              let take := min geo alg
              for c in [:take] do
                cols := cols ++ [getColumn N c]
                diagEntries := diagEntries ++ [simplify lam]
          if cols.length != n then
            return .defective s!"not diagonalizable: found {cols.length} eigenvectors, need {n}"
          match fromColumns cols with
          | none => return .error "failed to assemble P from eigenvectors"
          | some P0 =>
            let P := simpMat P0
            match det P with
            | none => return .error "det(P) failed"
            | some d =>
              if isZeroE d then
                return .defective "eigenvectors are linearly dependent (det P = 0)"
              else
                let D := diagonal diagEntries
                return .ok P (simpMat D)

/-- Modal matrix `P` only. -/
def modalMatrix (A : Array (Array Expr)) : Except String (Array (Array Expr)) :=
  match diagonalize A with
  | .ok P _ => pure P
  | .defective msg => throw msg
  | .error msg => throw msg

/-- Diagonal form `D = P⁻¹ A P`. -/
def diagonalForm (A : Array (Array Expr)) : Except String (Array (Array Expr)) :=
  match diagonalize A with
  | .ok _ D => pure D
  | .defective msg => throw msg
  | .error msg => throw msg

/-- Scalar exponential on matrix entries (constants: exp(0)=1). -/
def entryExp (e : Expr) : Expr :=
  let e := simplify e
  match e with
  | const c =>
    if c.isZero then Expr.one
    else Expr.exp (const c)
  | e => Expr.exp e

/--
  Matrix exponential for diagonalizable `A`:
  `expm(A) = P · exp(D) · P⁻¹` where `A = P D P⁻¹`.
-/
def expm (A : Array (Array Expr)) : Except String (Array (Array Expr)) :=
  match diagonalize A with
  | .defective msg => throw s!"expm: {msg}"
  | .error msg => throw s!"expm: {msg}"
  | .ok P D =>
    match mapDiagonal D entryExp with
    | none => throw "expm: bad diagonal"
    | some eD =>
      let eD := simpMat eD
      match inv P with
      | none => throw "expm: P is singular"
      | some Pinv =>
        let Pinv := simpMat Pinv
        match mul P eD with
        | none => throw "expm: P·exp(D) shape error"
        | some PeD =>
          match mul PeD Pinv with
          | none => throw "expm: (P·exp(D))·P⁻¹ shape error"
          | some R => pure (simpMat R)

end Taschenrechner.Mat
