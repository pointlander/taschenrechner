/-
  Bivariate polynomials over ℚ and resultants.

  A `BiPoly` is a polynomial in the **main** variable whose coefficients are
  univariate `Poly`s in the **secondary** variable:
    ∑_i  coeffs[i](secondary) · main^i

  Used for eliminating one variable from a 2-equation algebraic system.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Poly
import Taschenrechner.RatInt

namespace Taschenrechner

open Expr

/-- Polynomial in `main` with coefficients in `Poly` (secondary). -/
structure BiPoly where
  coeffs : Array Poly
  deriving Repr, Inhabited

namespace BiPoly

def zero : BiPoly := ⟨#[]⟩
def one  : BiPoly := ⟨#[Poly.one]⟩

def strip (p : BiPoly) : BiPoly :=
  Id.run do
    let mut cs := p.coeffs
    while cs.size > 0 && Poly.isZero cs.back! do
      cs := cs.pop
    pure ⟨cs⟩

def deg (p : BiPoly) : Int :=
  let p := strip p
  if p.coeffs.isEmpty then -1 else (p.coeffs.size : Int) - 1

def isZero (p : BiPoly) : Bool := strip p |>.coeffs.isEmpty

def coeff (p : BiPoly) (i : Nat) : Poly :=
  p.coeffs[i]?.getD Poly.zero

def lc (p : BiPoly) : Poly :=
  let p := strip p
  if p.coeffs.isEmpty then Poly.zero else p.coeffs.back!

/-- Constant (degree 0 in main and secondary). -/
def ofRat (c : RatConst) : BiPoly :=
  if c.isZero then zero else ⟨#[Poly.ofConst c]⟩

/-- Secondary-only polynomial (degree 0 in main). -/
def ofSecondary (p : Poly) : BiPoly :=
  let p := Poly.strip p
  if p.isZero then zero else ⟨#[p]⟩

/-- `main^k`. -/
def mainPow (k : Nat) : BiPoly :=
  if k == 0 then one
  else ⟨Array.replicate k Poly.zero |>.push Poly.one⟩

/-- Scale by a secondary poly. -/
def scale (c : Poly) (p : BiPoly) : BiPoly :=
  if c.isZero then zero
  else strip ⟨p.coeffs.map (fun a => Poly.mul c a)⟩

def add (a b : BiPoly) : BiPoly :=
  Id.run do
    let n := max a.coeffs.size b.coeffs.size
    let mut cs : Array Poly := Array.replicate n Poly.zero
    for i in [:n] do
      cs := cs.set! i (Poly.add (coeff a i) (coeff b i))
    pure (strip ⟨cs⟩)

def neg (p : BiPoly) : BiPoly :=
  ⟨p.coeffs.map Poly.neg⟩

def sub (a b : BiPoly) : BiPoly := add a (neg b)

def mul (a b : BiPoly) : BiPoly :=
  if a.isZero || b.isZero then zero
  else
    Id.run do
      let n := a.coeffs.size + b.coeffs.size - 1
      let mut cs : Array Poly := Array.replicate n Poly.zero
      for i in [:a.coeffs.size] do
        for j in [:b.coeffs.size] do
          let k := i + j
          cs := cs.set! k (Poly.add cs[k]! (Poly.mul a.coeffs[i]! b.coeffs[j]!))
      pure (strip ⟨cs⟩)

def powNat (p : BiPoly) (n : Nat) : BiPoly :=
  match n with
  | 0 => one
  | n'+1 => mul (powNat p n') p

instance : Add BiPoly where add := add
instance : Mul BiPoly where mul := mul
instance : Neg BiPoly where neg := neg
instance : Sub BiPoly where sub := sub

/-- Substitute main := `y0` (rational) → poly in secondary. -/
def evalMain (p : BiPoly) (y0 : RatConst) : Poly :=
  -- Horner
  let p := strip p
  Id.run do
    let mut acc := Poly.zero
    let mut i := p.coeffs.size
    while i > 0 do
      i := i - 1
      acc := Poly.add (Poly.mul acc (Poly.ofConst y0)) p.coeffs[i]!
    pure (Poly.strip acc)

/-- Substitute secondary := `x0` → univariate poly in main (as `Poly`). -/
def evalSecondary (p : BiPoly) (x0 : RatConst) : Poly :=
  let p := strip p
  Id.run do
    let mut cs : Array RatConst := Array.empty
    for i in [:p.coeffs.size] do
      cs := cs.push (Poly.eval p.coeffs[i]! x0)
    pure (Poly.strip ⟨cs⟩)

/-! ### Determinant of a matrix over `Poly` (Laplace) -/

partial def detPoly (M : Array (Array Poly)) : Poly :=
  let n := M.size
  if n == 0 then Poly.one
  else if n == 1 then Poly.strip (M[0]![0]!)
  else if n == 2 then
    -- ad − bc
    Poly.sub (Poly.mul M[0]![0]! M[1]![1]!) (Poly.mul M[0]![1]! M[1]![0]!)
  else
    -- expand along first row
    Id.run do
      let mut acc := Poly.zero
      for j in [:n] do
        let a0j := M[0]![j]!
        if !a0j.isZero then
          -- minor delete row 0, col j
          let mut minor : Array (Array Poly) := Array.empty
          for i in [1:n] do
            let mut row : Array Poly := Array.empty
            for k in [:n] do
              if k != j then row := row.push M[i]![k]!
            minor := minor.push row
          let d := detPoly minor
          let term := Poly.mul a0j d
          -- sign (-1)^j
          if j % 2 == 0 then acc := Poly.add acc term
          else acc := Poly.sub acc term
      pure (Poly.strip acc)

/-- Sylvester matrix of `f`, `g` w.r.t. main (size (m+n)×(m+n)). -/
def sylvester (f g : BiPoly) : Option (Array (Array Poly)) :=
  let f := strip f; let g := strip g
  let m := f.deg
  let n := g.deg
  if m < 0 || n < 0 then none
  else if m == 0 && n == 0 then
    -- Res = 1 by convention? or f0^0 * ... actually Res(a,b)=1 for nonzero constants
    some #[#[Poly.one]]
  else
    let mN := m.toNat
    let nN := n.toNat
    let dim := mN + nN
    if dim == 0 then some #[#[Poly.one]]
    else
      some <| Id.run do
        let mut M : Array (Array Poly) :=
          Array.replicate dim (Array.replicate dim Poly.zero)
        -- n rows for f-shifts
        for row in [:nN] do
          for k in [:mN + 1] do
            let col := row + k
            if col < dim then
              M := M.set! row ((M[row]!).set! col (coeff f (mN - k)))
        -- m rows for g-shifts
        for row in [:mN] do
          let r := nN + row
          for k in [:nN + 1] do
            let col := row + k
            if col < dim then
              M := M.set! r ((M[r]!).set! col (coeff g (nN - k)))
        pure M

/--
  Resultant of `f` and `g` with respect to main, as a poly in secondary.
  Uses the Sylvester determinant.
-/
def resultantMain (f g : BiPoly) : Poly :=
  let f := strip f; let g := strip g
  if f.isZero || g.isZero then Poly.zero
  else if f.deg == 0 then
    -- Res(a, g) = a^{deg g}
    match Poly.powNat (lc f) g.deg.toNat with
    | p => p
  else if g.deg == 0 then
    match Poly.powNat (lc g) f.deg.toNat with
    | p => p
  else
    match sylvester f g with
    | none => Poly.zero
    | some M => Poly.strip (detPoly M)

/--
  Parse a polynomial expression in two free variables into a `BiPoly`.
  Only +, −, *, integer powers, and constants / the two variables.
-/
partial def ofExpr? (e : Expr) (main sec : String) : Option BiPoly :=
  go (simplify e)
where
  go : Expr → Option BiPoly
  | Expr.add a b =>
    match go a, go b with
    | some pa, some pb => some (BiPoly.add pa pb)
    | _, _ => none
  | Expr.mul a b =>
    match go a, go b with
    | some pa, some pb => some (BiPoly.mul pa pb)
    | _, _ => none
  | Expr.pow base (Expr.const c) =>
    match CplxConst.toRat? c with
    | some q =>
      if q.den == 1 && q.num ≥ 0 then
        match go base with
        | some p => some (powNat p q.num.toNat)
        | none => none
      else none
    | none => none
  | Expr.var name =>
    if name == main then some (mainPow 1)
    else if name == sec then some (ofSecondary Poly.X)
    else none
  | Expr.const c =>
    match CplxConst.toRat? c with
    | some r => some (ofRat r)
    | none => none
  | _ => none

/-- Clear denominators: if `e` is a ratio of bivariate polys, return numerator. -/
def residualPoly? (e : Expr) (main sec : String) : Option BiPoly :=
  let e := simplify e
  match ofExpr? e main sec with
  | some p => some p
  | none =>
    match e with
    | Expr.mul a (Expr.pow _b (Expr.const c)) =>
      match CplxConst.toRat? c with
      | some q =>
        if q == RatConst.negOne then ofExpr? a main sec
        else none
      | none => none
    | _ => none

end BiPoly

end Taschenrechner
