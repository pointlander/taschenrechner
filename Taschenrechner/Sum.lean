/-
  Finite summation closed forms.

  * Polynomial summands via Faulhaber formulas (powers 0…6)
  * Geometric series ∑ r^k
  * Constant summands
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Solve
import Taschenrechner.Normal
import Taschenrechner.Eval

namespace Taschenrechner

open Expr

/-- `n` as a free variable (default upper limit name). -/
def sumN : Expr := var "n"

/--
  Closed form for ∑_{k=1}^n k^m as a polynomial expression in free var `nExpr`.
  Supports m = 0…6.
-/
def sumPowClosed (m : Nat) (nExpr : Expr) : Option Expr :=
  let n := nExpr
  let n2 := pow n (ofInt 2)
  let n3 := pow n (ofInt 3)
  let n4 := pow n (ofInt 4)
  let n5 := pow n (ofInt 5)
  let n6 := pow n (ofInt 6)
  let n7 := pow n (ofInt 7)
  match m with
  | 0 =>
    -- ∑ 1 = n
    some n
  | 1 =>
    -- n(n+1)/2
    some (simplify (div (mul n (add n one)) (ofInt 2)))
  | 2 =>
    -- n(n+1)(2n+1)/6
    some (simplify (div (mul (mul n (add n one)) (add (mul (ofInt 2) n) one)) (ofInt 6)))
  | 3 =>
    -- [n(n+1)/2]^2
    some (simplify (pow (div (mul n (add n one)) (ofInt 2)) (ofInt 2)))
  | 4 =>
    -- n(n+1)(2n+1)(3n²+3n−1)/30
    let a := mul (mul n (add n one)) (add (mul (ofInt 2) n) one)
    let b := add (add (mul (ofInt 3) n2) (mul (ofInt 3) n)) (ofInt (-1))
    some (simplify (div (mul a b) (ofInt 30)))
  | 5 =>
    -- n²(n+1)²(2n²+2n−1)/12
    let a := mul (pow n (ofInt 2)) (pow (add n one) (ofInt 2))
    let b := add (add (mul (ofInt 2) n2) (mul (ofInt 2) n)) (ofInt (-1))
    some (simplify (div (mul a b) (ofInt 12)))
  | 6 =>
    -- n(n+1)(2n+1)(3n⁴+6n³−3n+1)/42
    let a := mul (mul n (add n one)) (add (mul (ofInt 2) n) one)
    let b := add (add (add (mul (ofInt 3) n4) (mul (ofInt 6) n3))
      (mul (ofInt (-3)) n)) one
    some (simplify (div (mul a b) (ofInt 42)))
  | _ =>
    let _ := n5; let _ := n6; let _ := n7
    none

/-- ∑_{k=1}^{hi} k^m − ∑_{k=1}^{lo−1} k^m. -/
def sumPowRange (m : Nat) (lo hi : Expr) : Option Expr :=
  match sumPowClosed m hi with
  | none => none
  | some Fhi =>
    -- F(lo−1)
    let loPrev := simplify (sub lo one)
    match sumPowClosed m loPrev with
    | none => none
    | some Flo => some (simplify (sub Fhi Flo))

/--
  Sum of a polynomial in index `k` from `lo` to `hi` (inclusive),
  using Faulhaber for each monomial.
-/
def sumPoly (p : Poly) (lo hi : Expr) : Option Expr :=
  let p := Poly.strip p
  if p.isZero then some zero
  else
    Id.run do
      let mut acc : Option Expr := some zero
      for i in [:p.coeffs.size] do
        let c := p.coeffs[i]!
        if !c.isZero then
          match acc, sumPowRange i lo hi with
          | some a, some s =>
            let term :=
              if c.isOne then s
              else mul (ofRat c) s
            acc := some (simplify (add a term))
          | _, _ => acc := none
      pure acc

/-- Geometric sum ∑_{k=lo}^{hi} r^k. -/
def sumGeometric (r lo hi : Expr) : Option Expr :=
  let r := simplify r
  let lo := simplify lo
  let hi := simplify hi
  -- r = 1 → count of terms
  if r == one then
    some (simplify (add (sub hi lo) one))
  else
    -- r^lo * (1 − r^{hi−lo+1}) / (1 − r)
    let count := add (sub hi lo) one
    let rLo := pow r lo
    let rPow := pow r count
    let num := mul rLo (sub one rPow)
    let den := sub one r
    some (simplify (div num den))

/--
  Try to interpret `body` as a summand in free index `k`:
  * polynomial in `k`
  * geometric `r^k` with `r` independent of `k`
  * constant (independent of `k`)
-/
def sumBody (body : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  let body := simplify body
  if !dependsOn body k then
    -- constant c: c * (hi − lo + 1)
    some (simplify (mul body (add (sub hi lo) one)))
  else
    match body with
    | pow base (var name) =>
      if name == k && !dependsOn base k then
        sumGeometric base lo hi
      else
        match asPolyIn? body k with
        | some p => sumPoly p lo hi
        | none => none
    | pow (var name) expn =>
      if name == k then
        match asRatConst expn with
        | some q =>
          if q.den == 1 && q.num ≥ 0 then
            sumPowRange q.num.toNat lo hi
          else
            match asPolyIn? body k with
            | some p => sumPoly p lo hi
            | none => none
        | none =>
          match asPolyIn? body k with
          | some p => sumPoly p lo hi
          | none => none
      else
        match asPolyIn? body k with
        | some p => sumPoly p lo hi
        | none => none
    | _ =>
      match asPolyIn? body k with
      | some p => sumPoly p lo hi
      | none => none
where
  asRatConst : Expr → Option RatConst
    | const c => CplxConst.toRat? c
    | _ => none

/-- Integer constant? -/
def asIntConstExpr : Expr → Option Int
  | const c =>
    match CplxConst.toRat? c with
    | some q => if q.den == 1 then some q.num else none
    | none => none
  | _ => none

/-- Brute-force ∑_{k=lo}^{hi} body when bounds are integers (exact eval). -/
def sumBrute (body : Expr) (k : String) (lo hi : Int) : Option Expr :=
  if hi < lo then some zero
  else
    Id.run do
      let mut acc : Expr := zero
      let mut i := lo
      -- fuel: at most 10_000 terms
      let mut steps : Nat := 0
      while i ≤ hi && steps < 10000 do
        let term := simplify (subst body k (ofInt i))
        match eval? term with
        | some c => acc := simplify (add acc (const c))
        | none =>
          -- keep symbolic term if ground simplify failed partially
          acc := simplify (add acc term)
        i := i + 1
        steps := steps + 1
      if i ≤ hi then pure none else pure (some (simplify acc))

/--
  Finite sum ∑_{k=lo}^{hi} body.
  Returns `none` if no closed form is available.
  When `lo`/`hi` are integers, evaluates the closed form (or brute-forces).
-/
def sumFinite (body : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  let lo := simplify lo
  let hi := simplify hi
  match sumBody body k lo hi with
  | some s =>
    let s := simplify s
    match asIntConstExpr lo, asIntConstExpr hi with
    | some _, some _ =>
      -- Concrete bounds: prefer exact eval of closed form
      match eval? s with
      | some c => some (const c)
      | none =>
        -- closed form may still mention free vars incorrectly; brute force
        match asIntConstExpr lo, asIntConstExpr hi with
        | some a, some b =>
          match sumBrute body k a b with
          | some t => some t
          | none => some s
        | _, _ => some s
    | _, _ => some s
  | none =>
    -- No Faulhaber/geometric form: try brute force on integer bounds
    match asIntConstExpr lo, asIntConstExpr hi with
    | some a, some b => sumBrute body k a b
    | _, _ => none

/-- Sum with fallback message via Except. -/
def sumFiniteExpr (body : Expr) (k : String) (lo hi : Expr) : Except String Expr :=
  match sumFinite body k lo hi with
  | some s => pure s
  | none => throw s!"no closed form for sum over {k} of {body}"

end Taschenrechner
