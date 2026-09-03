/-
  Characteristic polynomial, eigenvalues, eigenspaces, and Jordan form.

  * `charpoly A` = det(t I − A) (monic in `t` by default)
  * `eigenvalues A` — roots of the char poly (rational, quadratic, cubic, quartic)
  * `eigenspace A λ` — nullspace of (A − λ I)
  * `jordanForm A` — `P⁻¹ A P = J` (Jordan blocks; charpoly must split)
  * `expm A` — `P exp(J) P⁻¹` (diagonalizable or defective)
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

/-! ### Jordan form (generalized eigenspaces) -/

def jordanMaxN : Nat := 8

def natFact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * natFact n

def kerDim (K : Array (Array Expr)) : Nat :=
  if K.isEmpty then 0 else ncols K

def toColumns (M : Array (Array Expr)) : List (Array Expr) :=
  let nc := kerDim M
  if nc == 0 || nrows M == 0 then []
  else (List.range nc).map (fun c => getColumn M c)

def isZeroCol (v : Array Expr) : Bool :=
  v.all isZeroE

def columnRank (cols : List (Array Expr)) : Nat :=
  if cols.isEmpty then 0
  else
    match fromColumns cols with
    | none => 0
    | some M => rank (simpMat M)

def independentMod (span : List (Array Expr)) (v : Array Expr) : Bool :=
  if isZeroCol v then false
  else columnRank (span ++ [v]) > columnRank span

def mulVec (M : Array (Array Expr)) (v : Array Expr) : Option (Array Expr) :=
  match fromColumns [v] with
  | none => none
  | some c =>
    match mul M c with
    | none => none
    | some r => some (getColumn (simpMat r) 0)

def applyPow (B : Array (Array Expr)) (j : Nat) (v : Array Expr) : Option (Array Expr) :=
  Id.run do
    let mut w? : Option (Array Expr) := some v
    for _ in [:j] do
      match w? with
      | none => pure ()
      | some w => w? := mulVec B w
    pure w?

def asRatLam? (e : Expr) : Option RatConst :=
  match simplify e with
  | const c => CplxConst.toRat? c
  | _ => none

/-- How many times `(X − r)` divides `p`. -/
def exactDivCount (p : Poly) (r : RatConst) : Nat :=
  let lin : Poly := ⟨#[RatConst.neg r, RatConst.one]⟩
  Id.run do
    let mut q := Poly.strip p
    let mut m : Nat := 0
    for _ in [:q.coeffs.size] do
      match Poly.exactDiv q lin with
      | some q' =>
        q := q'
        m := m + 1
      | none => return m
    pure m

def algMulOf (rs : List Expr) (lam : Expr) (cp? : Option Poly) : Nat :=
  let listed := algMultiplicity rs lam
  match asRatLam? lam, cp? with
  | some r, some p => max listed (exactDivCount p r)
  | _, _ => listed

/-- Jordan block: `λ` on the diagonal, `1` on the superdiagonal. -/
def jordanBlock (lam : Expr) (s : Nat) : Array (Array Expr) :=
  let lam := simplify lam
  Id.run do
    let mut rows : Array (Array Expr) := Array.empty
    for i in [:s] do
      let mut row : Array Expr := Array.empty
      for j in [:s] do
        if i == j then row := row.push lam
        else if j == i + 1 then row := row.push Expr.one
        else row := row.push Expr.zero
      rows := rows.push row
    pure rows

/-- Block-diagonal assembly. -/
def blockDiag (bs : List (Array (Array Expr))) : Array (Array Expr) :=
  let n := bs.foldl (fun acc b => acc + nrows b) 0
  if n == 0 then #[]
  else
    Id.run do
      let mut rows : Array (Array Expr) :=
        Array.replicate n (Array.replicate n Expr.zero)
      let mut off : Nat := 0
      for b in bs do
        let s := nrows b
        for i in [:s] do
          for j in [:s] do
            let row := rows[off + i]!
            rows := rows.set! (off + i) (row.set! (off + j) (get! b i j))
        off := off + s
      pure rows

/--
  `exp(t (λ I + N)) = e^{λ t} ∑ (t N)^k / k!`.
  Superdiagonal `k` holds `e^{λ t} t^k / k!`.
-/
def expJordanBlock (lam : Expr) (s : Nat) (t : Expr) : Array (Array Expr) :=
  let scale := entryExp (simplify (Expr.mul (simplify lam) t))
  let t := simplify t
  Id.run do
    let mut rows : Array (Array Expr) := Array.empty
    for i in [:s] do
      let mut row : Array Expr := Array.empty
      for j in [:s] do
        if j < i then
          row := row.push Expr.zero
        else
          let k := j - i
          let tk :=
            if k == 0 then Expr.one
            else if k == 1 then t
            else Expr.pow t (Expr.ofNat k)
          let den := natFact k
          let frac :=
            if den == 1 then tk
            else Expr.mul tk (Expr.ofRat ⟨1, den⟩)
          row := row.push (simplify (Expr.mul scale frac))
      rows := rows.push row
    pure rows

inductive JordanResult where
  | ok (P : Array (Array Expr)) (J : Array (Array Expr)) (blocks : List (Expr × Nat))
  | error (msg : String)
  deriving Repr, Inhabited

namespace JordanResult

def toExpr? : JordanResult → Except String Expr
  | .ok P J _ => pure (Expr.mat #[#[Expr.mat (simpMat P), Expr.mat (simpMat J)]])
  | .error msg => throw msg

end JordanResult

/--
  Jordan form of square `A` when the characteristic polynomial splits:
  chains in `ker(A−λI)^k`, `P⁻¹ A P = J` block-diagonal.
-/
def jordanForm (A : Array (Array Expr)) : JordanResult :=
  let n := nrows A
  if n == 0 || n != ncols A then .error "jordan: expected square matrix"
  else if n > jordanMaxN then .error s!"jordan: matrix larger than {jordanMaxN}×{jordanMaxN}"
  else
    match eigenvalues A with
    | none => .error "jordan: could not compute eigenvalues"
    | some rs =>
      let cp? : Option Poly :=
        match charpoly A charVar with
        | none => none
        | some e => asPolyIn? e charVar
      let uniq := uniqueEigenvalues rs
      if uniq.isEmpty then .error "jordan: no eigenvalues"
      else
        Id.run do
          let mut cols : List (Array Expr) := []
          let mut blocks : List (Expr × Nat) := []
          for lam in uniq do
            let alg := algMulOf rs lam cp?
            if alg == 0 then
              pure ()
            else
              match shiftByEigenvalue A (simplify lam) with
              | none => return .error s!"jordan: shift failed for {lam}"
              | some B0 =>
                let B := simpMat B0
                let mut kers : Array (Array (Array Expr)) := #[]
                for k in [1:alg + 1] do
                  match powNat B k with
                  | none => return .error "jordan: matrix power failed"
                  | some Bk =>
                    let K := nullspace (simpMat Bk)
                    kers := kers.push K
                    if kerDim K ≥ alg then break
                if kers.isEmpty then
                  return .error s!"jordan: empty generalized eigenspace for {lam}"
                let mut used : List (Array Expr) := []
                for idx in [:kers.size] do
                  let k := kers.size - idx
                  let Kprev : List (Array Expr) :=
                    if k ≤ 1 then [] else toColumns kers[k - 2]!
                  let cands := toColumns kers[k - 1]!
                  for v in cands do
                    if independentMod (used ++ Kprev) v then
                      match applyPow B (k - 1) v with
                      | none => return .error "jordan: chain apply failed"
                      | some v1 =>
                        if isZeroCol v1 then
                          pure ()
                        else
                          let mut chain : List (Array Expr) := []
                          let mut ok := true
                          for j in [:k] do
                            match applyPow B (k - 1 - j) v with
                            | none => ok := false
                            | some pj => chain := chain ++ [pj]
                          if !ok then
                            return .error "jordan: incomplete chain"
                          else
                            cols := cols ++ chain
                            used := used ++ chain
                            blocks := blocks ++ [(simplify lam, k)]
          if cols.length != n then
            return .error s!"jordan: assembled {cols.length} columns, need {n}"
          match fromColumns cols with
          | none => return .error "jordan: failed to assemble P"
          | some P0 =>
            let P := simpMat P0
            match det P with
            | none => return .error "jordan: det(P) failed"
            | some d =>
              if isZeroE d then
                return .error "jordan: P is singular"
              else
                let J := simpMat (blockDiag (blocks.map fun (lam, s) => jordanBlock lam s))
                return .ok P J blocks

/-- Jordan `P` only. -/
def jordanModal (A : Array (Array Expr)) : Except String (Array (Array Expr)) :=
  match jordanForm A with
  | .ok P _ _ => pure P
  | .error msg => throw msg

/-- Jordan canonical matrix `J`. -/
def jordanCanonical (A : Array (Array Expr)) : Except String (Array (Array Expr)) :=
  match jordanForm A with
  | .ok _ J _ => pure J
  | .error msg => throw msg

/-- `exp(t J)` for a Jordan matrix described by its blocks. -/
def expJordanBlocks (blocks : List (Expr × Nat)) (t : Expr) : Array (Array Expr) :=
  simpMat (blockDiag (blocks.map fun (lam, s) => expJordanBlock lam s t))

/-- `P · M · P⁻¹`. -/
def conjugate (P M : Array (Array Expr)) : Except String (Array (Array Expr)) :=
  match inv P with
  | none => throw "singular P"
  | some Pinv =>
    let Pinv := simpMat Pinv
    match mul P M with
    | none => throw "P·M shape error"
    | some PM =>
      match mul PM Pinv with
      | none => throw "(P·M)·P⁻¹ shape error"
      | some R => pure (simpMat R)

/--
  Matrix exponential: `expm(A) = P exp(J) P⁻¹` via Jordan form
  (includes the diagonalizable case as 1×1 blocks).
-/
def expm (A : Array (Array Expr)) : Except String (Array (Array Expr)) :=
  match jordanForm A with
  | .error msg => throw s!"expm: {msg}"
  | .ok P _ blocks =>
    conjugate P (expJordanBlocks blocks Expr.one)

/-- Fundamental matrix `expm(A x) = P exp(J x) P⁻¹`. -/
def expmAt (A : Array (Array Expr)) (t : Expr) : Except String (Array (Array Expr)) :=
  match jordanForm A with
  | .error msg => throw msg
  | .ok P _ blocks =>
    conjugate P (expJordanBlocks blocks t)

end Taschenrechner.Mat
