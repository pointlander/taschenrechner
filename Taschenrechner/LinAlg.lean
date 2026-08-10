/-
  Symbolic Gaussian elimination: RREF, rank, nullspace, and linear solve
  (including general solutions with free parameters).

  Lives in a separate module so it can call `Expr.simplify` without a
  circular import with `Simplify` → `Matrix`.
-/
import Taschenrechner.Simplify
import Taschenrechner.Matrix
import Taschenrechner.Normal

namespace Taschenrechner.Mat

open Expr

/-- Simplify an entry (normal form for more stable pivots). -/
def simp (e : Expr) : Expr := Expr.normalForm e

/-- Algebraic zero test via normal forms (for pivots / elimination). -/
def isZeroE (e : Expr) : Bool :=
  Expr.isZeroExpr e

/-- Deep-copy matrix rows. -/
def clone (rows : Array (Array Expr)) : Array (Array Expr) :=
  rows.map (fun row => row.map id)

/-- Swap rows `i` and `j`. -/
def swapRows (rows : Array (Array Expr)) (i j : Nat) : Array (Array Expr) :=
  if i == j then rows
  else
    let ri := rows[i]!
    let rj := rows[j]!
    rows.set! i rj |>.set! j ri

/-- Scale row `i` by scalar `c`. -/
def scaleRow (rows : Array (Array Expr)) (i : Nat) (c : Expr) : Array (Array Expr) :=
  let row := rows[i]!.map fun e => simp (Expr.mul c e)
  rows.set! i row

/-- row_i := row_i + c * row_k -/
def addScaledRow (rows : Array (Array Expr)) (i k : Nat) (c : Expr) : Array (Array Expr) :=
  if isZeroE c then rows
  else
    Id.run do
      let ri := rows[i]!
      let rk := rows[k]!
      let mut newRow : Array Expr := Array.empty
      for j in [:ri.size] do
        newRow := newRow.push (simp (Expr.add ri[j]! (Expr.mul c rk[j]!)))
      pure (rows.set! i newRow)

/--
  Reduced row echelon form (Gauss–Jordan) over symbolic entries.
  Pivots are scaled to 1; entries above/below pivots cleared.
-/
partial def rref (rows0 : Array (Array Expr)) : Array (Array Expr) :=
  if rows0.isEmpty then rows0
  else
    let m := nrows rows0
    let n := ncols rows0
    Id.run do
      let mut rows := clone rows0 |>.map (fun row => row.map simp)
      let mut pivotRow : Nat := 0
      for col in [:n] do
        if pivotRow >= m then break
        -- find pivot
        let mut pivot := pivotRow
        let mut found := false
        for r in [pivotRow:m] do
          if !isZeroE (get! rows r col) then
            pivot := r
            found := true
            break
        if !found then
          pure ()
        else
          rows := swapRows rows pivotRow pivot
          let piv := get! rows pivotRow col
          -- scale pivot row to make pivot 1
          if !(simp piv == Expr.one) then
            let invPiv := Expr.div Expr.one piv
            rows := scaleRow rows pivotRow invPiv
          -- eliminate column
          for r in [:m] do
            if r != pivotRow then
              let factor := get! rows r col
              if !isZeroE factor then
                rows := addScaledRow rows r pivotRow (Expr.neg factor)
          pivotRow := pivotRow + 1
      pure (rows.map (fun row => row.map simp))

/-- Rank = number of nonzero rows in RREF. -/
def rank (rows : Array (Array Expr)) : Nat :=
  let R := rref rows
  Id.run do
    let mut r : Nat := 0
    for row in R do
      if row.any (fun e => !isZeroE e) then r := r + 1
    pure r

/-! ### Pivot analysis of an RREF matrix -/

/--
  Pivot structure of an RREF matrix with `nVars` variable columns
  (for augmented systems, pass `ncols - 1`; for plain A, pass `ncols`).
-/
structure PivotInfo where
  /-- For each row: pivot column, if any. -/
  pivotColOfRow : Array (Option Nat)
  /-- `used[j] = true` if column j is a pivot column. -/
  isPivotCol    : Array Bool
  /-- Free (non-pivot) variable indices. -/
  freeCols      : Array Nat
  deriving Repr

/-- Analyze pivots in the left `nVars` columns of an RREF matrix. -/
def analyzePivots (R : Array (Array Expr)) (nVars : Nat) : PivotInfo :=
  let m := nrows R
  Id.run do
    let mut pivotColOfRow : Array (Option Nat) := Array.replicate m none
    let mut isPivotCol : Array Bool := Array.replicate nVars false
    for i in [:m] do
      let row := R[i]!
      let mut found : Option Nat := none
      for j in [:nVars] do
        if found.isNone && j < row.size && !isZeroE row[j]! then
          found := some j
      pivotColOfRow := pivotColOfRow.set! i found
      match found with
      | some j => isPivotCol := isPivotCol.set! j true
      | none => pure ()
    let mut freeCols : Array Nat := Array.empty
    for j in [:nVars] do
      if !isPivotCol[j]! then
        freeCols := freeCols.push j
    pure { pivotColOfRow, isPivotCol, freeCols }

/-- Name of the k-th free parameter (1-based): `t1`, `t2`, … -/
def freeParamName (k : Nat) : String := s!"t{k + 1}"

def freeParam (k : Nat) : Expr := Expr.var (freeParamName k)

/--
  Build one nullspace basis vector for free column `freeIdx`
  among `freeCols` (index into freeCols is `freePos`).
  Homogeneous RREF of A (no RHS column).
-/
def nullBasisVector (R : Array (Array Expr)) (info : PivotInfo) (freePos : Nat) (nVars : Nat) : Array Expr :=
  let freeCols := info.freeCols
  let freeIdx := freeCols[freePos]!
  Id.run do
    -- start with zeros; free var freeIdx = 1
    let mut x : Array Expr := Array.replicate nVars Expr.zero
    x := x.set! freeIdx Expr.one
    -- other free vars already 0
    -- basic vars from each pivot row: x_p = -sum_j R[i,j] x_j (homog)
    for i in [:nrows R] do
      match info.pivotColOfRow[i]! with
      | none => pure ()
      | some p =>
        if p < nVars then
          -- x_p = - R[i, freeIdx] * 1  (only freeIdx is 1 among free)
          let coef := get! R i freeIdx
          x := x.set! p (simp (Expr.neg coef))
    pure x

/--
  Nullspace basis of A as an n×k matrix (columns = basis vectors).
  Returns a  n×0 empty matrix concept as `zeros n 0` when trivial —
  we use 0 columns: empty row arrays of length 0, or special case.
-/
def nullspace (A : Array (Array Expr)) : Array (Array Expr) :=
  let n := ncols A
  if n == 0 then #[]
  else
    let R := rref A
    let info := analyzePivots R n
    let k := info.freeCols.size
    if k == 0 then
      -- trivial nullspace: n×0 — represent as empty array (0 columns)
      #[]
    else
      Id.run do
        -- build n×k by columns then transpose view: produce rows
        let mut cols : Array (Array Expr) := Array.empty
        for f in [:k] do
          cols := cols.push (nullBasisVector R info f n)
        -- cols[c][r] → rows[r][c]
        let mut rows : Array (Array Expr) := Array.empty
        for r in [:n] do
          let mut row : Array Expr := Array.empty
          for c in [:k] do
            row := row.push (cols[c]![r]!)
          rows := rows.push row
        pure rows

/-- Result of solving A x = b. -/
inductive SolveResult where
  /-- Unique solution as n×1 column. -/
  | unique (x : Array (Array Expr))
  /--
    General solution as n×1 column whose entries may contain free
    parameters `t1`, `t2`, … (affine: x_p + N t).
  -/
  | general (x : Array (Array Expr)) (numFree : Nat)
  | inconsistent (msg : String)
  | error (msg : String)
  deriving Repr, Inhabited

namespace SolveResult

def toString : SolveResult → String
  | unique x => s!"unique solution:\n{pretty x}"
  | general x k =>
    let params :=
      String.intercalate ", " ((List.range k).map freeParamName)
    s!"general solution ({k} free parameter(s): {params}):\n{pretty x}"
  | inconsistent msg => s!"inconsistent: {msg}"
  | error msg => s!"error: {msg}"

instance : ToString SolveResult where
  toString := toString

/-- Extract matrix if unique or general (for expression embedding). -/
def matrix? : SolveResult → Option (Array (Array Expr))
  | unique x => some x
  | general x _ => some x
  | _ => none

end SolveResult

/-- Normalize `b` to an m×1 column matrix. Accepts m×1 or 1×m. -/
def asColumn (b : Array (Array Expr)) (m : Nat) : Option (Array (Array Expr)) :=
  if nrows b == m && ncols b == 1 then some b
  else if nrows b == 1 && ncols b == m then
    some (transpose b)
  else if nrows b == m && ncols b == m && m == 1 then some b
  else none

/-- Build augmented matrix [A | b]. -/
def augment (A bcol : Array (Array Expr)) : Array (Array Expr) :=
  Id.run do
    let m := nrows A
    let mut out : Array (Array Expr) := Array.empty
    for i in [:m] do
      let mut row := A[i]!
      row := row.push (get! bcol i 0)
      out := out.push row
    pure out

/--
  From RREF of [A|b], build parametric solution column.
  Free variables become `t1`, `t2`, …
-/
def generalSolutionFromRref (R : Array (Array Expr)) (info : PivotInfo) (nVars : Nat) : Array (Array Expr) :=
  let freeCols := info.freeCols
  let k := freeCols.size
  Id.run do
    -- particular: free = 0, basic = RHS
    let mut x : Array Expr := Array.replicate nVars Expr.zero
    -- free vars = t_pos
    for f in [:k] do
      let j := freeCols[f]!
      x := x.set! j (freeParam f)
    -- pivot equations: x_p + sum_j R[i,j] x_j = R[i,n]
    -- x_p = R[i,n] - sum_{j ≠ p} R[i,j] x_j
    for i in [:nrows R] do
      match info.pivotColOfRow[i]! with
      | none => pure ()
      | some p =>
        if p < nVars then
          let row := R[i]!
          let rhs := if nVars < row.size then row[nVars]! else Expr.zero
          let mut acc : Expr := rhs
          for j in [:nVars] do
            if j != p then
              let coef := row[j]!
              if !isZeroE coef then
                -- acc -= coef * x_j
                acc := Expr.sub acc (Expr.mul coef x[j]!)
          x := x.set! p (simp acc)
    -- re-simplify all (dependencies: free set first then basic — one pass enough if we use free only in sum)
    -- Recompute basic vars once more using final free expressions
    for i in [:nrows R] do
      match info.pivotColOfRow[i]! with
      | none => pure ()
      | some p =>
        if p < nVars then
          let row := R[i]!
          let rhs := if nVars < row.size then row[nVars]! else Expr.zero
          let mut acc : Expr := rhs
          for j in [:nVars] do
            if j != p then
              let coef := row[j]!
              if !isZeroE coef then
                acc := Expr.sub acc (Expr.mul coef x[j]!)
          x := x.set! p (simp acc)
    pure (x.map fun e => #[simp e])

/--
  Solve A x = b for square or rectangular A.

  * Unique → n×1 column of constants/expressions
  * Underdetermined consistent → general solution with free params `t1`, `t2`, …
  * Inconsistent / shape errors reported explicitly
-/
def solve (A : Array (Array Expr)) (b : Array (Array Expr)) : SolveResult :=
  let m := nrows A
  let n := ncols A
  if m == 0 then .error "empty coefficient matrix"
  else
    match asColumn b m with
    | none => .error s!"b must be {m}×1 (or 1×{m}); got {nrows b}×{ncols b}"
    | some bcol =>
      let aug := augment A bcol
      let R := rref aug
      let info := analyzePivots R n
      -- inconsistency: [0 ... 0 | c] with c ≠ 0
      Id.run do
        let mut bad := false
        for i in [:m] do
          let row := R[i]!
          let mut allZeroLeft := true
          for j in [:n] do
            if !isZeroE row[j]! then allZeroLeft := false
          if allZeroLeft && n < row.size && !isZeroE row[n]! then
            bad := true
        if bad then
          pure (.inconsistent "0 = nonzero after elimination")
        else if info.freeCols.isEmpty then
          -- unique
          let mut xvals : Array Expr := Array.replicate n Expr.zero
          for i in [:m] do
            match info.pivotColOfRow[i]! with
            | some j =>
              if j < n then
                xvals := xvals.set! j (simp (get! R i n))
            | none => pure ()
          pure (.unique (xvals.map fun e => #[e]))
        else
          let x := generalSolutionFromRref R info n
          pure (.general x info.freeCols.size)

/-- Convenience: matrix if unique or general. -/
def solveMat? (A b : Array (Array Expr)) : Option (Array (Array Expr)) :=
  (solve A b).matrix?

/-- Nullity = number of free variables = dim nullspace. -/
def nullity (A : Array (Array Expr)) : Nat :=
  (analyzePivots (rref A) (ncols A)).freeCols.size

end Taschenrechner.Mat
