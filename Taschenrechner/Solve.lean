/-
  Scalar polynomial solving and factoring over ℚ.

  * `factor` — factor polynomials / rationals in one variable (and small integers)
  * `roots` / `solve` — rational roots + quadratic formula for remaining deg-2 pieces
  * `coeff` / `collect` — coefficient extraction and poly collection
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Normal

namespace Taschenrechner

open Expr

/-! ### Helpers -/

/-- Integer square root test for a non-negative rational. -/
def ratSqrt? (r : RatConst) : Option RatConst :=
  let r := RatConst.normalize r
  if r.num < 0 then none
  else
    let sn := Nat.sqrt r.num.natAbs
    let sd := Nat.sqrt r.den
    if sn * sn == r.num.natAbs && sd * sd == r.den && sd ≠ 0 then
      some (RatConst.normalize ⟨(sn : Int), sd⟩)
    else none

/-- Trial factorization of a positive natural. -/
partial def factorNat (n : Nat) : List (Nat × Nat) :=
  if n ≤ 1 then []
  else
    let rec go (n p : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
      if n == 1 then acc.reverse
      else if p * p > n then
        if n > 1 then ((n, 1) :: acc).reverse else acc.reverse
      else if n % p == 0 then
        let rec count (n e : Nat) : Nat × Nat :=
          if n % p == 0 then count (n / p) (e + 1) else (n, e)
        let (n', e) := count n 0
        go n' (p + 1) ((p, e) :: acc)
      else go n (p + 1) acc
    go n 2 []

/--
  Factor a non-zero integer as a matrix of `[prime, exponent]` rows
  (survives auto-`simplify`, which would fold `2^2·3` back to `12`).
  Negative `n` gets a leading row `[-1, 1]`.
-/
def factorInt (n : Int) : Expr :=
  if n == 0 then Expr.zero
  else if n == 1 then Expr.one
  else if n == -1 then Expr.negOne
  else
    let facs := factorNat n.natAbs
    let rows : List (Array Expr) :=
      facs.map fun (p, e) => #[Expr.ofNat p, Expr.ofNat e]
    let rows :=
      if n < 0 then #[Expr.ofInt (-1), Expr.ofNat 1] :: rows else rows
    if rows.isEmpty then Expr.one
    else Expr.mat rows.toArray

/-- Convert expression to a polynomial in `v` (clears a constant denominator). -/
def asPolyIn? (e : Expr) (v : String) : Option Poly :=
  match RatFn.ofExpr? (simplify e) v with
  | none => none
  | some r =>
    let r := RatFn.simplify r
    if r.num.isZero then some Poly.zero
    else if r.den.isOne then some (Poly.strip r.num)
    else if r.den.deg == 0 then
      let d := Poly.coeff r.den 0
      match RatConst.inv d with
      | some inv => some (Poly.strip (Poly.scale inv r.num))
      | none => none
    else
      -- rational: zeros of num (excluding poles); use numerator
      some (Poly.strip r.num)

/-- Build monic linear factor `x − r`. -/
def linearFactor (v : String) (r : RatConst) : Expr :=
  if r.isZero then var v
  else if r.isNegOne then add (var v) one
  else if r.num < 0 then
    -- x - (-|r|) = x + |r|
    add (var v) (ofRat (RatConst.neg r))
  else
    sub (var v) (ofRat r)

/-- Group equal monic factors with multiplicity. -/
def groupFactors (fs : List Poly) : List (Poly × Nat) :=
  let rec insert (p : Poly) : List (Poly × Nat) → List (Poly × Nat)
    | [] => [(p, 1)]
    | (q, m) :: rest =>
      if p == q then (q, m + 1) :: rest
      else (q, m) :: insert p rest
  fs.foldl (fun acc p => insert (Poly.monic p) acc) []

/-- Product of (poly factor expressions) with multiplicities. -/
def factorsToExpr (c : RatConst) (facs : List (Poly × Nat)) (v : String) : Expr :=
  let body :=
    facs.foldl (fun acc (p, m) =>
      let pe := Poly.toExpr p v
      let pe := if m == 1 then pe else pow pe (Expr.ofNat m)
      if acc == Expr.one then pe else mul acc pe) Expr.one
  if c.isOne then body
  else if c.isZero then Expr.zero
  else if body == Expr.one then Expr.ofRat c
  else mul (Expr.ofRat c) body

/-! ### Factor -/

/-- Factor a univariate polynomial/rational expression over ℚ in variable `v`. -/
def factorIn (e : Expr) (v : String) : Option Expr :=
  let e := simplify e
  -- pure integer constant
  match e with
  | const c =>
    match CplxConst.toRat? c with
    | some q =>
      if q.den == 1 then some (factorInt q.num)
      else
        -- p/q: return factor matrices is awkward; leave as factored ints product
        -- via num/den integer matrices is unclear — emit (factor num)/(factor den)
        -- only when both are ±1 or use poly path; for fractions use num/den ints.
        some (div (factorInt q.num) (factorInt (Int.ofNat q.den)))
    | none => some e  -- complex constant: leave
  | _ =>
    match RatFn.ofExpr? e v with
    | none => none
    | some r =>
      let r := RatFn.simplify r
      if r.num.isZero then some Expr.zero
      else
        let (cn, nFacs) := Poly.factorOverQ r.num
        let (cd, dFacs) := Poly.factorOverQ r.den
        let nG := groupFactors nFacs
        let dG := groupFactors dFacs
        -- Do not `simplify` the product: that would reassemble integers
        -- (2²·3 → 12) and can expand linear factors.
        let numE := factorsToExpr cn nG v
        if r.den.isOne || (dFacs.isEmpty && cd.isOne) then
          some numE
        else
          let denE := factorsToExpr cd dG v
          some (div numE denE)

def factor (e : Expr) (v : String := "x") : Expr :=
  match factorIn e v with
  | some f => f
  | none => simplify e

/-! ### Roots & solve -/

/-- Extract rational roots (with multiplicity) from factorOverQ linear factors. -/
def rationalRoots (p : Poly) : List RatConst :=
  let (_c, facs) := Poly.factorOverQ p
  facs.filterMap fun f =>
    let f := Poly.monic (Poly.strip f)
    -- monic linear: x − r  ≡  ⟨−r, 1⟩
    if f.deg == 1 && (Poly.coeff f 1).isOne then
      some (RatConst.neg (Poly.coeff f 0))
    else none

/-- Quadratic formula for `a x² + b x + c = 0` with `a ≠ 0`. -/
def quadraticRoots (a b c : RatConst) : List Expr :=
  match RatConst.inv a with
  | none => []
  | some _ =>
    let disc := b * b - RatConst.ofInt 4 * a * c
    let twoA := RatConst.ofInt 2 * a
    match RatConst.inv twoA with
    | none => []
    | some inv2a =>
      let negB := RatConst.neg b
      if disc.isZero then
        [Expr.ofRat (negB * inv2a)]
      else
        match ratSqrt? disc with
        | some s =>
          [Expr.ofRat ((negB + s) * inv2a), Expr.ofRat ((negB - s) * inv2a)]
        | none =>
          if disc.num < 0 then
            -- complex: (-b ± i √|disc|) / (2a)
            match ratSqrt? (RatConst.neg disc) with
            | some s =>
              let re := Expr.ofRat (negB * inv2a)
              let im := Expr.ofRat (s * inv2a)
              let iim := mul I im
              [simplify (add re iim), simplify (sub re iim)]
            | none =>
              -- fallback symbolic sqrt of negative
              let s := sqrt (Expr.ofRat (RatConst.neg disc))
              let re := Expr.ofRat (negB * inv2a)
              let im := simplify (mul (Expr.ofRat inv2a) s)
              let iim := mul I im
              [simplify (add re iim), simplify (sub re iim)]
          else
            -- real irrational
            let s := sqrt (Expr.ofRat disc)
            let half := Expr.ofRat inv2a
            let mid := Expr.ofRat (negB * inv2a)
            [simplify (add mid (mul half s)), simplify (sub mid (mul half s))]

/--
  Roots of a univariate poly over ℚ, with quadratic formula for irreducible
  quadratics. Higher-degree irreducibles yield no closed roots here.
-/
def rootsPoly (p : Poly) : List Expr :=
  let p := Poly.strip p
  if p.isZero then []  -- identity; handled by caller
  else if p.deg < 0 then []
  else if p.deg == 0 then []  -- non-zero constant: no roots
  else
    let (c, facs) := Poly.factorOverQ p
    let _ := c
    Id.run do
      let mut out : List Expr := []
      for f in facs do
        let f := Poly.monic (Poly.strip f)
        if f.deg == 1 && (Poly.coeff f 1).isOne then
          out := Expr.ofRat (RatConst.neg (Poly.coeff f 0)) :: out
        else if f.deg == 2 then
          let a := Poly.coeff f 2
          let b := Poly.coeff f 1
          let c0 := Poly.coeff f 0
          out := quadraticRoots a b c0 ++ out
        else
          pure ()
      pure out.reverse

inductive ScalarSolveResult where
  /-- Finite list of solutions. -/
  | solutions : List Expr → ScalarSolveResult
  /-- Every value is a solution (0 = 0). -/
  | all : ScalarSolveResult
  /-- No solutions (non-zero constant = 0). -/
  | empty : ScalarSolveResult
  /-- Could not interpret as a univariate rational equation. -/
  | unsupported : String → ScalarSolveResult
  deriving Repr

namespace ScalarSolveResult

def toExpr : ScalarSolveResult → Expr
  | .solutions rs =>
    -- 1×n row matrix of roots (empty → 1×0)
    Expr.mat #[rs.toArray]
  | .all => var "all"  -- marker; parser may special-case
  | .empty => Expr.mat #[#[] ]
  | .unsupported _ => Expr.zero

def toString : ScalarSolveResult → String
  | .solutions rs =>
    if rs.isEmpty then "∅"
    else String.intercalate ", " (rs.map fun r => s!"{r}")
  | .all => "all (identity)"
  | .empty => "∅ (no solution)"
  | .unsupported msg => s!"unsupported: {msg}"

end ScalarSolveResult

/-- Solve `e = 0` as a univariate rational equation in `v`. -/
def solveScalar (e : Expr) (v : String) : ScalarSolveResult :=
  let e := simplify e
  match asPolyIn? e v with
  | none => .unsupported s!"not a rational expression in {v}"
  | some p =>
    let p := Poly.strip p
    if p.isZero then .all
    else if p.deg == 0 then .empty  -- non-zero constant
    else
      let rs := rootsPoly p
      -- If deg > 2 irreducible pieces remain unsolved, still return what we found
      .solutions (rs.map simplify)

/-- Solve `lhs = rhs` in `v`. -/
def solveEq (lhs rhs : Expr) (v : String) : ScalarSolveResult :=
  solveScalar (sub lhs rhs) v

/-- Roots of `e = 0` as a list (empty if none / identity / unsupported). -/
def roots (e : Expr) (v : String := "x") : List Expr :=
  match solveScalar e v with
  | .solutions rs => rs
  | _ => []

/--
  Convert a scalar solve result to an expression for the REPL:
  * finite roots → 1×n matrix
  * empty → empty row matrix
  * all → the symbol `all` (variable)
  * unsupported → error via Option
-/
def solveScalarExpr? (e : Expr) (v : String) : Except String Expr :=
  match solveScalar e v with
  | .solutions rs => pure (Expr.mat #[rs.toArray])
  | .all => pure (var "all")
  | .empty => pure (Expr.mat #[#[] ])
  | .unsupported msg => throw msg

def solveEqExpr? (lhs rhs : Expr) (v : String) : Except String Expr :=
  solveScalarExpr? (sub lhs rhs) v

/-! ### coeff / collect -/

/-- Coefficient of `v^n` in a polynomial/rational (num after clear const den). -/
def coeffOf (e : Expr) (v : String) (n : Nat) : Option Expr :=
  match asPolyIn? e v with
  | some p => some (Expr.ofRat (Poly.coeff p n))
  | none => none

/-- Collect terms as a canonical polynomial in `v` (when possible). -/
def collectIn (e : Expr) (v : String) : Option Expr :=
  match asPolyIn? e v with
  | some p => some (simplify (Poly.toExpr p v))
  | none =>
    match RatFn.ofExpr? (simplify e) v with
    | some r => some (RatFn.toExpr (RatFn.simplify r) v)
    | none => none

def collect (e : Expr) (v : String := "x") : Expr :=
  match collectIn e v with
  | some f => f
  | none => simplify e

end Taschenrechner
