/-
  Symbolic Gaussian elimination: RREF, rank, and linear solve.

  Lives in a separate module so it can call `Expr.simplify` without a
  circular import with `Simplify` → `Matrix`.
-/
import Taschenrechner.Simplify
import Taschenrechner.Matrix

namespace Taschenrechner.Mat

open Expr

/-- Simplify an entry. -/
def simp (e : Expr) : Expr := Expr.simplify e

/-- Structural/algebraic zero test after simplification. -/
def isZeroE (e : Expr) : Bool :=
  let e := simp e
  match e with
  | const c => c.isZero
  | _ => e == Expr.zero

/-- Deep-copy matrix rows. -/
def clone (rows : Array (Array Expr)) : Array (Array Expr) :=
  rows.map (fun row => row.map id)

/-- Swap rows `i` and `j` in place (mutates array of rows). -/
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

/-- Result of solving A x = b. -/
inductive SolveResult where
  | unique (x : Array (Array Expr))
    -- n×1 column
  | infinite (msg : String)
  | inconsistent (msg : String)
  | error (msg : String)
  deriving Repr, Inhabited

namespace SolveResult

def toString : SolveResult → String
  | unique x => s!"unique solution:\n{pretty x}"
  | infinite msg => s!"infinitely many solutions: {msg}"
  | inconsistent msg => s!"inconsistent: {msg}"
  | error msg => s!"error: {msg}"

instance : ToString SolveResult where
  toString := toString

end SolveResult

/-- Normalize `b` to an m×1 column matrix. Accepts m×1 or 1×m. -/
def asColumn (b : Array (Array Expr)) (m : Nat) : Option (Array (Array Expr)) :=
  if nrows b == m && ncols b == 1 then some b
  else if nrows b == 1 && ncols b == m then
    -- row vector → column
    some (transpose b)
  else if nrows b == m && ncols b == m && m == 1 then some b
  else none

/--
  Solve A x = b for square or rectangular A.
  Returns a unique solution when RREF determines all variables;
  reports infinite/inconsistent otherwise.
-/
def solve (A : Array (Array Expr)) (b : Array (Array Expr)) : SolveResult :=
  let m := nrows A
  let n := ncols A
  if m == 0 then .error "empty coefficient matrix"
  else
    match asColumn b m with
    | none => .error s!"b must be {m}×1 (or 1×{m}); got {nrows b}×{ncols b}"
    | some bcol =>
      -- augment [A | b]
      let aug : Array (Array Expr) :=
        Id.run do
          let mut out : Array (Array Expr) := Array.empty
          for i in [:m] do
            let mut row := A[i]!
            row := row.push (get! bcol i 0)
            out := out.push row
          pure out
      let R := rref aug
      Id.run do
        -- detect inconsistency: [0 ... 0 | c] with c ≠ 0
        let mut inconsistent := false
        for i in [:m] do
          let row := R[i]!
          let mut allZeroLeft := true
          for j in [:n] do
            if !isZeroE row[j]! then allZeroLeft := false
          if allZeroLeft && !isZeroE row[n]! then
            inconsistent := true
        if inconsistent then
          pure (.inconsistent "0 = nonzero after elimination")
        else
          -- find pivot column for each row
          let mut pivotCol : Array (Option Nat) := Array.replicate m none
          let mut used : Array Bool := Array.replicate n false
          for i in [:m] do
            let row := R[i]!
            let mut found : Option Nat := none
            for j in [:n] do
              if found.isNone && !isZeroE row[j]! then
                found := some j
            pivotCol := pivotCol.set! i found
            match found with
            | some j => used := used.set! j true
            | none => pure ()
          -- free variables?
          let mut hasFree := false
          for j in [:n] do
            if !used[j]! then hasFree := true
          if hasFree then
            pure (.infinite "free variables remain (underdetermined or dependent columns)")
          else
            -- unique: x_j = R[i][n] where pivotCol[i] = j
            let mut xvals : Array Expr := Array.replicate n Expr.zero
            for i in [:m] do
              match pivotCol[i]! with
              | some j => xvals := xvals.set! j (simp (get! R i n))
              | none => pure ()
            let xcol := xvals.map fun e => #[e]
            pure (.unique xcol)

/-- Convenience: solve and return matrix expression if unique. -/
def solveMat? (A b : Array (Array Expr)) : Option (Array (Array Expr)) :=
  match solve A b with
  | .unique x => some x
  | _ => none

end Taschenrechner.Mat
