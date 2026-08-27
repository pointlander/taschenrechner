/-
  Finite summation closed forms.

  * Polynomial summands via Faulhaber / Bernoulli numbers (all powers)
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

/-- Highest power for which Bernoulli/Faulhaber is computed (arbitrary-precision, but slow). -/
def faulhaberMaxM : Nat := 64

/-- Binomial coefficient `C(n, k)`. -/
def natBinom (n k : Nat) : Nat :=
  if k > n then 0
  else
    let k := min k (n - k)
    Id.run do
      let mut r : Nat := 1
      for i in [:k] do
        r := r * (n - i) / (i + 1)
      pure r

/--
  Bernoulli numbers `B_0, …, B_m` with `B_1 = −1/2`
  (power-sum convention: `∑_{k=0}^n C(n+1,k) B_k = 0` for `n ≥ 1`).
-/
def bernoulliList (m : Nat) : Array RatConst :=
  Id.run do
    let mut B : Array RatConst := Array.replicate (m + 1) RatConst.zero
    B := B.set! 0 RatConst.one
    for n in [1:m + 1] do
      let mut s := RatConst.zero
      for k in [:n] do
        let c := RatConst.ofInt (Int.ofNat (natBinom (n + 1) k))
        s := s + c * B[k]!
      match RatConst.div (RatConst.neg s) (RatConst.ofInt (Int.ofNat (n + 1))) with
      | some bn => B := B.set! n bn
      | none => pure ()
    pure B

def bernoulli (n : Nat) : RatConst :=
  (bernoulliList n)[n]!

/--
  Closed form for `∑_{k=1}^n k^m` as a polynomial in `nExpr`.

  Faulhaber: `1/(m+1) ∑_{j=0}^m (-1)^j C(m+1,j) B_j n^{m+1−j}`
  with `B_1 = −1/2`.
-/
def sumPowClosed (m : Nat) (nExpr : Expr) : Option Expr :=
  if m > faulhaberMaxM then none
  else
    let Bs := bernoulliList m
    let den := RatConst.ofInt (Int.ofNat (m + 1))
    Id.run do
      let mut acc : Expr := zero
      for j in [:m + 1] do
        let sign : Int := if j % 2 == 0 then 1 else -1
        let bin := RatConst.ofInt (Int.ofNat (natBinom (m + 1) j))
        let Bj := Bs[j]!
        let raw := RatConst.ofInt sign * bin * Bj
        match RatConst.div raw den with
        | none => pure ()
        | some ck =>
          if !ck.isZero then
            let p := m + 1 - j
            let np :=
              if p == 0 then one
              else if p == 1 then nExpr
              else pow nExpr (ofNat p)
            let term := if ck.isOne then np else mul (ofRat ck) np
            acc := add acc term
      pure (some (simplify acc))

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
