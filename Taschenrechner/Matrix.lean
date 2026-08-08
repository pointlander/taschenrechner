/-
  Symbolic matrices over `Expr` entries.

  Supports addition, scalar/matrix multiplication, transpose, trace,
  determinant (Laplace expansion), and inverse via adjugate when det ≠ 0.
-/
import Taschenrechner.Expr

namespace Taschenrechner

open Expr

namespace Mat

/-- Number of rows. -/
def nrows (rows : Array (Array Expr)) : Nat := rows.size

/-- Number of columns (0 if empty). -/
def ncols (rows : Array (Array Expr)) : Nat :=
  if rows.isEmpty then 0 else rows[0]!.size

def isRectangular (rows : Array (Array Expr)) : Bool :=
  if rows.isEmpty then true
  else
    let n := rows[0]!.size
    rows.all (fun r => r.size == n)

def ofLists (xss : List (List Expr)) : Except String (Array (Array Expr)) := do
  if xss.isEmpty then throw "empty matrix"
  let rows := xss.toArray.map (·.toArray)
  if !isRectangular rows then throw "ragged matrix (unequal row lengths)"
  pure rows

def get! (rows : Array (Array Expr)) (i j : Nat) : Expr :=
  rows[i]![j]!

def map (rows : Array (Array Expr)) (f : Expr → Expr) : Array (Array Expr) :=
  rows.map (fun row => row.map f)

def zipWith (a b : Array (Array Expr)) (f : Expr → Expr → Expr) : Option (Array (Array Expr)) :=
  if a.size != b.size then none
  else if a.isEmpty then some #[]
  else if ncols a != ncols b then none
  else
    some <| Id.run do
      let mut out : Array (Array Expr) := Array.empty
      for i in [:a.size] do
        let ra := a[i]!; let rb := b[i]!
        let mut row : Array Expr := Array.empty
        for j in [:ra.size] do
          row := row.push (f ra[j]! rb[j]!)
        out := out.push row
      pure out

def add (a b : Array (Array Expr)) : Option (Array (Array Expr)) :=
  zipWith a b Expr.add

def sub (a b : Array (Array Expr)) : Option (Array (Array Expr)) :=
  zipWith a b Expr.sub

def scale (c : Expr) (a : Array (Array Expr)) : Array (Array Expr) :=
  map a (fun e => Expr.mul c e)

def transpose (rows : Array (Array Expr)) : Array (Array Expr) :=
  let m := nrows rows
  let n := ncols rows
  if m == 0 then #[]
  else
    Id.run do
      let mut out : Array (Array Expr) := Array.empty
      for j in [:n] do
        let mut row : Array Expr := Array.empty
        for i in [:m] do
          row := row.push (get! rows i j)
        out := out.push row
      pure out

def zeros (m n : Nat) : Array (Array Expr) :=
  Array.replicate m (Array.replicate n Expr.zero)

def ones (m n : Nat) : Array (Array Expr) :=
  Array.replicate m (Array.replicate n Expr.one)

def eye (n : Nat) : Array (Array Expr) :=
  Id.run do
    let mut out : Array (Array Expr) := Array.empty
    for i in [:n] do
      let mut row : Array Expr := Array.empty
      for j in [:n] do
        row := row.push (if i == j then Expr.one else Expr.zero)
      out := out.push row
    pure out

def mul (a b : Array (Array Expr)) : Option (Array (Array Expr)) :=
  let m := nrows a
  let n := ncols a
  let p := ncols b
  if n != nrows b then none
  else if m == 0 || p == 0 then some #[]
  else
    some <| Id.run do
      let mut out : Array (Array Expr) := Array.empty
      for i in [:m] do
        let mut row : Array Expr := Array.empty
        for j in [:p] do
          let mut acc : Expr := Expr.zero
          for k in [:n] do
            acc := Expr.add acc (Expr.mul (get! a i k) (get! b k j))
          row := row.push acc
        out := out.push row
      pure out

/-- Trace of a square matrix. -/
def trace (rows : Array (Array Expr)) : Option Expr :=
  let n := nrows rows
  if n == 0 || n != ncols rows then none
  else
    some <| Id.run do
      let mut acc : Expr := Expr.zero
      for i in [:n] do
        acc := Expr.add acc (get! rows i i)
      pure acc

/-- Minor: delete row `i` and column `j`. -/
def minor (rows : Array (Array Expr)) (i j : Nat) : Array (Array Expr) :=
  Id.run do
    let mut out : Array (Array Expr) := Array.empty
    for r in [:nrows rows] do
      if r != i then
        let mut row : Array Expr := Array.empty
        let src := rows[r]!
        for c in [:src.size] do
          if c != j then row := row.push src[c]!
        out := out.push row
    pure out

/-- Determinant via Laplace expansion along the first row. -/
partial def det (rows : Array (Array Expr)) : Option Expr :=
  let n := nrows rows
  if n == 0 || n != ncols rows then none
  else if n == 1 then some (get! rows 0 0)
  else if n == 2 then
    -- ad - bc
    let a := get! rows 0 0; let b := get! rows 0 1
    let c := get! rows 1 0; let d := get! rows 1 1
    some (Expr.sub (Expr.mul a d) (Expr.mul b c))
  else
    Id.run do
      let mut acc : Expr := Expr.zero
      for j in [:n] do
        match det (minor rows 0 j) with
        | none => return none
        | some m =>
          let entry := get! rows 0 j
          let term := Expr.mul entry m
          -- cofactor sign (-1)^{0+j}
          let signed :=
            if j % 2 == 0 then term else Expr.neg term
          acc := Expr.add acc signed
      pure (some acc)

/-- Cofactor matrix C_{ij} = (-1)^{i+j} M_{ij}. -/
partial def cofactorMatrix (rows : Array (Array Expr)) : Option (Array (Array Expr)) :=
  let n := nrows rows
  if n == 0 || n != ncols rows then none
  else
    Id.run do
      let mut out : Array (Array Expr) := Array.empty
      for i in [:n] do
        let mut row : Array Expr := Array.empty
        for j in [:n] do
          match det (minor rows i j) with
          | none => return none
          | some m =>
            let signed := if (i + j) % 2 == 0 then m else Expr.neg m
            row := row.push signed
        out := out.push row
      pure (some out)

/-- Inverse via adjugate: A^{-1} = (1/det A) · adj(A)^T. -/
partial def inv (rows : Array (Array Expr)) : Option (Array (Array Expr)) :=
  match det rows with
  | none => none
  | some d =>
    if d == Expr.zero then none
    else
      match cofactorMatrix rows with
      | none => none
      | some c =>
        let adj := transpose c
        some (scale (Expr.div Expr.one d) adj)

/-- Integer power of a square matrix (non-negative). -/
partial def powNat (rows : Array (Array Expr)) (k : Nat) : Option (Array (Array Expr)) :=
  let n := nrows rows
  if n == 0 || n != ncols rows then none
  else
    match k with
    | 0 => some (eye n)
    | k'+1 =>
      match powNat rows k' with
      | none => none
      | some p => mul p rows

/-- Pretty multi-line matrix (for CLI). -/
def pretty (rows : Array (Array Expr)) : String :=
  let cells : Array (Array String) :=
    rows.map (fun row => row.map (fun e => toString e))
  let colW : Array Nat :=
    if rows.isEmpty then #[]
    else
      Id.run do
        let n := ncols rows
        let mut ws : Array Nat := Array.replicate n 0
        for row in cells do
          for j in [:n] do
            ws := ws.set! j (max ws[j]! row[j]!.length)
        pure ws
  let lines := cells.toList.map fun row =>
    let parts := Id.run do
      let mut ps : List String := []
      for j in [:row.size] do
        let s := row[j]!
        let pad := String.ofList (List.replicate (colW[j]! - s.length) ' ')
        ps := ps ++ [pad ++ s]
      pure ps
    "│ " ++ String.intercalate "  " parts ++ " │"
  if lines.isEmpty then "[]"
  else String.intercalate "\n" lines

end Mat

/-- Try to interpret expression as a matrix. -/
def asMat? : Expr → Option (Array (Array Expr))
  | .mat rows => if Mat.isRectangular rows then some rows else none
  | _ => none

end Taschenrechner
