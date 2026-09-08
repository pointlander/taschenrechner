/-
  Finite summation and products.

  * Polynomial summands via Faulhaber / Bernoulli numbers (all powers)
  * Geometric series ∑ r^k
  * Hypergeometric terms via Gosper (rational t(k) and p(k)·r^k)
  * Constant summands
  * Finite products ∏ via Pochhammer / Γ (linear factors), geometric r^k,
    rational telescoping, and numeric evaluation
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Solve
import Taschenrechner.Normal
import Taschenrechner.Eval
import Taschenrechner.Gosper

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

/-- Polynomial in `k` (not a non-constant rational). -/
def asPolyForSum? (e : Expr) (k : String) : Option Poly :=
  match RatFn.ofExpr? (simplify e) k with
  | none => none
  | some r =>
    let r := RatFn.simplify r
    if r.num.isZero then some Poly.zero
    else if r.den.isOne then some (Poly.strip r.num)
    else if r.den.deg == 0 then
      match RatConst.inv (Poly.coeff r.den 0) with
      | some inv => some (Poly.strip (Poly.scale inv r.num))
      | none => none
    else none

/--
  Try to interpret `body` as a summand in free index `k`:
  * polynomial in `k` (Faulhaber)
  * geometric `r^k` with `r` independent of `k`
  * hypergeometric (Gosper)
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
        match asPolyForSum? body k with
        | some p => sumPoly p lo hi
        | none => gosperSum body k lo hi
    | pow (var name) expn =>
      if name == k then
        match asRatConst expn with
        | some q =>
          if q.den == 1 && q.num ≥ 0 then
            sumPowRange q.num.toNat lo hi
          else
            match asPolyForSum? body k with
            | some p => sumPoly p lo hi
            | none => gosperSum body k lo hi
        | none =>
          match asPolyForSum? body k with
          | some p => sumPoly p lo hi
          | none => gosperSum body k lo hi
      else
        match asPolyForSum? body k with
        | some p => sumPoly p lo hi
        | none => gosperSum body k lo hi
    | _ =>
      match asPolyForSum? body k with
      | some p => sumPoly p lo hi
      | none => gosperSum body k lo hi
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
    -- No Faulhaber/geometric/Gosper form: try brute force on integer bounds
    match asIntConstExpr lo, asIntConstExpr hi with
    | some a, some b => sumBrute body k a b
    | _, _ => none

/-- Sum with fallback message via Except. -/
def sumFiniteExpr (body : Expr) (k : String) (lo hi : Expr) : Except String Expr :=
  match sumFinite body k lo hi with
  | some s => pure s
  | none => throw s!"no closed form for sum over {k} of {body}"

/-! ### Finite products -/

/-- Number of terms in `k = lo…hi` inclusive. -/
def rangeCount (lo hi : Expr) : Expr :=
  simplify (add (sub hi lo) one)

/-- `Γ(u+m) → (u+m−1)!` for positive integer `m`; `Γ(1) → 1`. -/
def gammaToNice (e : Expr) : Expr :=
  match simplify e with
  | gamma arg =>
    if arg == one then one
    else
      let fromAdd (u : Expr) (c : CplxConst) : Expr :=
        match CplxConst.toRat? c with
        | some q =>
          if q.den == 1 && q.num ≥ 1 then
            let m := q.num.toNat
            factorial (if m == 1 then u else add u (ofNat (m - 1)))
          else gamma arg
        | none => gamma arg
      match arg with
      | add u (const c) => fromAdd u c
      | add (const c) u => fromAdd u c
      | _ =>
        match asNat? arg with
        | some 0 => gamma arg
        | some n =>
          if n ≤ 21 then ofNat (factNat (n - 1)) else gamma arg
        | none => gamma arg
  | e => e

/-- `n! / (n+1)! → 1/(n+1)`, `(n+1)! / n! → n+1`. -/
def cancelFactRatio (e : Expr) : Expr :=
  let e := simplify e
  match e with
  | mul a b =>
    let tryCancel (u v : Expr) : Option Expr :=
      if simplify v == simplify (add u one) then some (simplify (div one v))
      else if simplify u == simplify (add v one) then some (simplify u)
      else none
    match a, b with
    | factorial u, pow (factorial v) (const r) =>
      match CplxConst.toRat? r with
      | some q =>
        if q == RatConst.negOne then
          match tryCancel u v with
          | some t => t
          | none => e
        else e
      | none => e
    | pow (factorial v) (const r), factorial u =>
      match CplxConst.toRat? r with
      | some q =>
        if q == RatConst.negOne then
          match tryCancel u v with
          | some t => t
          | none => e
        else e
      | none => e
    | _, _ => e
  | e => e

/-- `Γ(a)/Γ(b)` rewritten toward factorials, then cancelled. -/
def tidyGammaDiv (num den : Expr) : Expr :=
  cancelFactRatio (simplify (div (gammaToNice num) (gammaToNice den)))

/-- `∏_{k=lo}^{hi} (k + shift) = Γ(hi+shift+1) / Γ(lo+shift)`. -/
def pochFromTo (shift lo hi : Expr) : Expr :=
  let top := simplify (add hi (add shift one))
  let bot := simplify (add lo shift)
  tidyGammaDiv (gamma top) (gamma bot)

/-- Product of a polynomial that splits into linears over ℚ. -/
def prodPoly (p : Poly) (lo hi : Expr) : Option Expr :=
  let p := Poly.strip p
  let count := rangeCount lo hi
  if p.isZero then some zero
  else if p.deg == 0 then
    some (simplify (pow (ofRat (Poly.coeff p 0)) count))
  else
    let lc := Poly.lc p
    let (_c, facs) := Poly.factorOverQ p
    Id.run do
      let mut roots : List RatConst := []
      for f in facs do
        let f := Poly.monic (Poly.strip f)
        if f.deg == 1 && (Poly.coeff f 1).isOne then
          roots := RatConst.neg (Poly.coeff f 0) :: roots
        else if f.deg ≤ 0 then
          pure ()
        else
          return none
      let mut acc : Expr :=
        if lc.isOne then one else pow (ofRat lc) count
      for r in roots do
        let shift := ofRat (RatConst.neg r)
        acc := mul acc (pochFromTo shift lo hi)
      some (simplify acc)

/-- `∏_{k=lo}^{hi} r^k = r^{(lo+hi)(hi−lo+1)/2}`. -/
def prodGeometric (r lo hi : Expr) : Option Expr :=
  let r := simplify r
  let lo := simplify lo
  let hi := simplify hi
  let count := rangeCount lo hi
  if r == one then some one
  else if r == zero then
    -- 0^0 at k=0 is awkward; if lo > 0 the product is 0
    match asIntConstExpr lo with
    | some a => if a > 0 then some zero else none
    | none => none
  else
    let expo := simplify (div (mul (add lo hi) count) (ofInt 2))
    some (simplify (pow r expo))

/-- Polynomial or rational in `k` as a product of Pochhammers. -/
def prodPolyOrRat (e : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  match asPolyForSum? e k with
  | some p => prodPoly p lo hi
  | none =>
    match RatFn.ofExpr? (simplify e) k with
    | none => none
    | some rf =>
      let rf := RatFn.simplify rf
      match prodPoly rf.num lo hi, prodPoly rf.den lo hi with
      | some n, some d =>
        if d == zero then none
        else some (cancelFactRatio (simplify (div n d)))
      | _, _ => none

/-- One multiplicative factor (no flattening). -/
partial def prodOne (e : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  let e := simplify e
  let count := rangeCount lo hi
  if !dependsOn e k then
    some (simplify (pow e count))
  else
    match e with
    | pow base (var name) =>
      if name == k && !dependsOn base k then
        prodGeometric base lo hi
      else prodPolyOrRat e k lo hi
    | pow base expn =>
      if !dependsOn expn k then
        match prodOne base k lo hi with
        | some p => some (simplify (pow p expn))
        | none => prodPolyOrRat e k lo hi
      else if !dependsOn base k then
        match expn with
        | var name =>
          if name == k then prodGeometric base lo hi
          else prodPolyOrRat e k lo hi
        | _ => prodPolyOrRat e k lo hi
      else prodPolyOrRat e k lo hi
    | _ => prodPolyOrRat e k lo hi

/--
  Interpret `body` as a productand in index `k`:
  * constant `c` → `c^{hi−lo+1}`
  * geometric `r^k`
  * polynomial / rational splitting into linears (Pochhammer / Γ)
  * product of such factors
-/
def prodBody (body : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  let body := simplify body
  let fs := flattenMul body
  if fs.length ≥ 2 then
    Id.run do
      let mut acc : Expr := one
      for f in fs do
        match prodOne f k lo hi with
        | none => return prodPolyOrRat body k lo hi
        | some p => acc := mul acc p
      some (cancelFactRatio (simplify acc))
  else
    prodOne body k lo hi

/-- Brute-force `∏_{k=lo}^{hi} body` when bounds are integers. -/
def prodBrute (body : Expr) (k : String) (lo hi : Int) : Option Expr :=
  if hi < lo then some one
  else
    Id.run do
      let mut acc : Expr := one
      let mut i := lo
      let mut steps : Nat := 0
      while i ≤ hi && steps < 10000 do
        let term := simplify (subst body k (ofInt i))
        match eval? term with
        | some c =>
          if c.isZero then return some zero
          acc := simplify (mul acc (const c))
        | none =>
          acc := simplify (mul acc term)
        i := i + 1
        steps := steps + 1
      if i ≤ hi then none else some (simplify acc)

/-- Finite product `∏_{k=lo}^{hi} body`. -/
def prodFinite (body : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  let lo := simplify lo
  let hi := simplify hi
  match asIntConstExpr lo, asIntConstExpr hi with
  | some a, some b =>
    if b < a then some one
    else
      match prodBody body k lo hi with
      | some s =>
        let s := cancelFactRatio (simplify s)
        match eval? s with
        | some c => some (const c)
        | none =>
          match prodBrute body k a b with
          | some t => some t
          | none => some s
      | none => prodBrute body k a b
  | _, _ =>
    match prodBody body k lo hi with
    | some s => some (cancelFactRatio (simplify s))
    | none => none

/-- Product with fallback message via Except. -/
def prodFiniteExpr (body : Expr) (k : String) (lo hi : Expr) : Except String Expr :=
  match prodFinite body k lo hi with
  | some s => pure s
  | none => throw s!"no closed form for product over {k} of {body}"

end Taschenrechner
