/-
  Univariate polynomials over ℚ (`RatConst`), with Euclidean arithmetic,
  resultants, and Yun square-free factorization.

  Used by the Risch rational / transcendental integrator.
-/
import Taschenrechner.Expr

namespace Taschenrechner

namespace RatConst

def abs (r : RatConst) : RatConst :=
  if r.num < 0 then neg r else r

def compare (a b : RatConst) : Ordering :=
  let a := normalize a; let b := normalize b
  -- a.num/a.den ? b.num/b.den
  let lhs := a.num * (b.den : Int)
  let rhs := b.num * (a.den : Int)
  if lhs < rhs then .lt else if lhs > rhs then .gt else .eq

def lt (a b : RatConst) : Bool := compare a b == .lt
def le (a b : RatConst) : Bool := compare a b != .gt

/-- Exact division when `b` divides `a` in ℚ (always if b ≠ 0). -/
def div! (a b : RatConst) : RatConst :=
  match div a b with
  | some r => r
  | none => zero

end RatConst

/-- Univariate polynomial with coefficients in ℚ, low degree first. -/
structure Poly where
  coeffs : Array RatConst
  deriving Repr, Inhabited

namespace Poly

def zero : Poly := ⟨#[]⟩
def one  : Poly := ⟨#[RatConst.one]⟩
def ofConst (c : RatConst) : Poly :=
  if c.isZero then zero else ⟨#[c]⟩
def ofInt (n : Int) : Poly := ofConst (RatConst.ofInt n)
def X : Poly := ⟨#[RatConst.zero, RatConst.one]⟩

def strip (p : Poly) : Poly :=
  Id.run do
    let mut cs := p.coeffs
    while cs.size > 0 && cs.back!.isZero do
      cs := cs.pop
    pure ⟨cs⟩

def deg (p : Poly) : Int :=
  let p := strip p
  if p.coeffs.isEmpty then -1 else (p.coeffs.size : Int) - 1

def isZero (p : Poly) : Bool := strip p |>.coeffs.isEmpty
def isOne (p : Poly) : Bool :=
  let p := strip p
  p.coeffs.size == 1 && p.coeffs[0]!.isOne

def coeff (p : Poly) (i : Nat) : RatConst :=
  p.coeffs[i]?.getD RatConst.zero

def lc (p : Poly) : RatConst :=
  let p := strip p
  if p.coeffs.isEmpty then RatConst.zero else p.coeffs.back!

def monic (p : Poly) : Poly :=
  let p := strip p
  if p.isZero then zero
  else
    let a := lc p
    match RatConst.inv a with
    | none => p
    | some inv => ⟨p.coeffs.map (· * inv)⟩

def beq (a b : Poly) : Bool :=
  let a := strip a; let b := strip b
  if a.coeffs.size != b.coeffs.size then false
  else
    Id.run do
      for i in [:a.coeffs.size] do
        if !(a.coeffs[i]! == b.coeffs[i]!) then return false
      pure true

instance : BEq Poly where beq := beq

def add (a b : Poly) : Poly :=
  Id.run do
    let n := max a.coeffs.size b.coeffs.size
    let mut cs : Array RatConst := Array.replicate n RatConst.zero
    for i in [:n] do
      cs := cs.set! i (coeff a i + coeff b i)
    pure (strip ⟨cs⟩)

def neg (p : Poly) : Poly := ⟨p.coeffs.map RatConst.neg⟩
def sub (a b : Poly) : Poly := add a (neg b)

def mul (a b : Poly) : Poly :=
  if a.isZero || b.isZero then zero
  else
    Id.run do
      let n := a.coeffs.size + b.coeffs.size - 1
      let mut cs : Array RatConst := Array.replicate n RatConst.zero
      for i in [:a.coeffs.size] do
        for j in [:b.coeffs.size] do
          let k := i + j
          cs := cs.set! k (cs[k]! + a.coeffs[i]! * b.coeffs[j]!)
      pure (strip ⟨cs⟩)

def scale (c : RatConst) (p : Poly) : Poly :=
  if c.isZero then zero else ⟨p.coeffs.map (c * ·)⟩

def powNat (p : Poly) (n : Nat) : Poly :=
  match n with
  | 0 => one
  | n'+1 => mul (powNat p n') p

/-- `X^n`. -/
def Xpow (n : Nat) : Poly :=
  if n == 0 then one
  else ⟨Array.replicate n RatConst.zero |>.push RatConst.one⟩

instance : Add Poly where add := add
instance : Sub Poly where sub := sub
instance : Mul Poly where mul := mul
instance : Neg Poly where neg := neg
instance : BEq Poly where beq := beq
instance : OfNat Poly n where ofNat := ofInt n

/-- Formal derivative. -/
def differentiate (p : Poly) : Poly :=
  let p := strip p
  if p.coeffs.size ≤ 1 then zero
  else
    Id.run do
      let mut cs : Array RatConst := Array.empty
      for i in [1:p.coeffs.size] do
        cs := cs.push (p.coeffs[i]! * RatConst.ofInt i)
      pure (strip ⟨cs⟩)

/-- Evaluate at a rational point. -/
def eval (p : Poly) (x : RatConst) : RatConst :=
  -- Horner
  let p := strip p
  Id.run do
    let mut acc := RatConst.zero
    let mut i := p.coeffs.size
    while i > 0 do
      i := i - 1
      acc := acc * x + p.coeffs[i]!
    pure acc

/-- Polynomial division: `a = q*b + r` with deg r < deg b (or r=0). -/
partial def divMod (a b : Poly) : Poly × Poly :=
  let b := strip b
  if b.isZero then (zero, strip a)
  else
    let lb := lc b
    let rec loop (q r : Poly) (fuel : Nat) : Poly × Poly :=
      match fuel with
      | 0 => (strip q, strip r)
      | fuel'+1 =>
        let r := strip r
        if r.isZero || r.deg < b.deg then (strip q, r)
        else
          match RatConst.div (lc r) lb with
          | none => (strip q, r)
          | some c =>
            let shift := (r.deg - b.deg).toNat
            let mono := scale c (Xpow shift)
            loop (add q mono) (sub r (mul mono b)) fuel'
    loop zero (strip a) 256

def divPoly (a b : Poly) : Poly := (divMod a b).1
def modPoly (a b : Poly) : Poly := (divMod a b).2

/-- Content: gcd of coefficient numerators / lcm of dens (primitive over ℤ then ℚ). -/
def content (p : Poly) : RatConst :=
  let p := strip p
  if p.isZero then RatConst.zero
  else
    -- gcd of all non-zero coeffs as rationals: content = gcd(nums)/lcm(dens) with signs
    Id.run do
      let mut g : Nat := 0
      let mut l : Nat := 1
      for c in p.coeffs do
        if !c.isZero then
          g := Nat.gcd g c.num.natAbs
          l := Nat.lcm l c.den
      if g == 0 then pure RatConst.zero
      else
        let lead := lc p
        let sign : Int := if lead.num < 0 then -1 else 1
        pure (RatConst.normalize ⟨sign * (g : Int), l⟩)

def primitivePart (p : Poly) : Poly :=
  let p := strip p
  if p.isZero then zero
  else
    let c := content p
    match RatConst.inv c with
    | none => p
    | some inv => scale inv p

/-- Euclidean GCD, monic. -/
partial def gcd (a b : Poly) : Poly :=
  let a := strip a; let b := strip b
  if b.isZero then monic a
  else if a.isZero then monic b
  else gcd b (modPoly a b)

def divides (a b : Poly) : Bool :=
  -- a | b ?
  if a.isZero then b.isZero
  else (modPoly b a).isZero

/-- Exact quotient when `b` divides `a`. -/
def exactDiv (a b : Poly) : Option Poly :=
  if b.isZero then none
  else
    let (q, r) := divMod a b
    if r.isZero then some (strip q) else none

/-- Pseudo-remainder sequence helper for resultant (subresultant-free Euclidean). -/
partial def resultant (a b : Poly) : RatConst :=
  let a := strip a; let b := strip b
  if a.isZero || b.isZero then
    if a.isZero && b.isZero then RatConst.zero
    else if a.deg == 0 then (if b.isZero then RatConst.zero else powLc a b.deg)
    else if b.deg == 0 then powLc b a.deg
    else RatConst.zero
  else
    go a b 1
where
  powLc (p : Poly) (n : Int) : RatConst :=
    if n ≤ 0 then RatConst.one
    else
      match RatConst.powInt (lc p) n with
      | some r => r
      | none => RatConst.zero
  go (a b : Poly) (sign : Int) : RatConst :=
    let a := strip a; let b := strip b
    if b.isZero then
      if a.deg == 0 then
        let c := lc a
        if sign < 0 then RatConst.neg c else c
      else RatConst.zero
    else
      let (q, r) := divMod a b
      let _ := q
      let da := a.deg
      let db := b.deg
      let oddSign := (da * db) % 2 != 0
      -- Res(a,b) = lc(b)^(deg a - deg r) * (-1)^(deg a * deg b) * Res(b,r)
      let r := strip r
      if r.isZero then
        if b.deg == 0 then
          let e := da
          match RatConst.powInt (lc b) e with
          | some p =>
            if oddSign then
              if sign < 0 then p else RatConst.neg p
            else
              if sign < 0 then RatConst.neg p else p
          | none => RatConst.zero
        else RatConst.zero
      else
        let dr := r.deg
        let exp := da - dr
        let lcPow :=
          match RatConst.powInt (lc b) exp with
          | some p => p
          | none => RatConst.one
        let s2 : Int := if oddSign then -sign else sign
        let rest := go b r s2
        lcPow * rest

/-- Sylvester-style resultant (more reliable for moderate degrees). -/
partial def resultant2 (p q : Poly) : RatConst :=
  let p := strip p; let q := strip q
  if p.isZero || q.isZero then
    if p.deg == 0 && !q.isZero then
      match RatConst.powInt (lc p) q.deg with | some r => r | none => .zero
    else if q.deg == 0 && !p.isZero then
      match RatConst.powInt (lc q) p.deg with | some r => r | none => .zero
    else .zero
  else if p.deg == 0 then
    match RatConst.powInt (lc p) q.deg with | some r => r | none => .zero
  else if q.deg == 0 then
    match RatConst.powInt (lc q) p.deg with | some r => r | none => .zero
  else
    -- Euclidean algorithm with degree tracking
    let rec eu (a b : Poly) (sign : RatConst) (fuel : Nat) : RatConst :=
      match fuel with
      | 0 => .zero
      | fuel'+1 =>
        let a := strip a; let b := strip b
        if b.isZero then
          if a.deg == 0 then sign * lc a else .zero
        else if b.deg == 0 then
          match RatConst.powInt (lc b) a.deg with
          | some pw => sign * pw
          | none => .zero
        else
          let da := a.deg
          let db := b.deg
          let r := modPoly a b
          let r := strip r
          -- sign flip (-1)^{deg a * deg b}
          let sign' :=
            if (da * db) % 2 != 0 then RatConst.neg sign else sign
          -- factor lc(b)^{deg a - deg r}
          if r.isZero then
            if db == 0 then sign' -- unreachable
            else .zero  -- common root / non-constant gcd
          else
            let exp := da - r.deg
            let factor :=
              match RatConst.powInt (lc b) exp with
              | some pw => pw
              | none => RatConst.one
            eu b r (sign' * factor) fuel'
    eu p q RatConst.one 64

/-- Prefer resultant2. -/
def res (a b : Poly) : RatConst := resultant2 a b

/-- Yun square-free factorization: `p = c * ∏ s_i^i` with monic square-free coprime `s_i`. -/
partial def squareFreeFactor (p : Poly) : RatConst × List (Poly × Nat) :=
  let p := strip p
  if p.isZero then (RatConst.zero, [])
  else
    let c := content p
    let p := primitivePart p |> monic
    let dp := differentiate p
    let g := gcd p dp
    if g.isOne || g.deg == 0 then
      (c, [(p, 1)])
    else
      match exactDiv p g with
      | none => (c, [(p, 1)])
      | some p1 =>
        -- Yun:
        -- p0 = p, d0 = p', g0 = gcd(p0,d0), p1 = p0/g0, d1 = d0/g0 - p1'
        -- then for i=1,2,... : gi = gcd(pi, di), si = pi/gi, pi+1 = gi, ...
        let d1 := sub (divPoly dp g) (differentiate p1)
        let factors := yun p1 d1 1 []
        (c, factors.reverse)
where
  yun (pi di : Poly) (i : Nat) (acc : List (Poly × Nat)) : List (Poly × Nat) :=
    if pi.isOne || pi.deg == 0 then acc
    else if i > 64 then acc
    else
      let gi := gcd pi di
      let si :=
        match exactDiv pi gi with
        | some s => monic s
        | none => monic pi
      let acc :=
        if si.isOne || si.deg == 0 then acc else (si, i) :: acc
      if gi.isOne || gi.deg == 0 then acc
      else
        let diNext :=
          match exactDiv di gi with
          | some d' => sub d' (differentiate gi)
          | none => zero
        yun gi diNext (i + 1) acc

/-- Rational root candidates ± factors(const)/factors(lc). -/
def rationalRootCandidates (p : Poly) : List RatConst :=
  let p := strip p
  if p.isZero || p.deg ≤ 0 then []
  else
    let a0 := coeff p 0
    let an := lc p
    let numFacts := intFactors a0.num
    let denFacts := intFactors an.num
    Id.run do
      let mut out : List RatConst := []
      for n in numFacts do
        for d in denFacts do
          if d != 0 then
            let r := RatConst.normalize ⟨n, d.natAbs⟩
            let r' := RatConst.neg r
            if !out.any (· == r) then out := r :: out
            if !out.any (· == r') then out := r' :: out
      pure out
where
  intFactors (n : Int) : List Int :=
    let n := n.natAbs
    if n == 0 then [0]
    else
      Id.run do
        let mut fs : List Int := []
        for i in [1:n+1] do
          if n % i == 0 then
            fs := (i : Int) :: (-(i : Int)) :: fs
        pure fs

/-- Factor into monic factors over ℚ by peeling rational linear factors, then
    leaving irreducible pieces (deg ≥ 2). Adequate for Hermite / partial fractions. -/
partial def factorOverQ (p : Poly) : RatConst × List Poly :=
  let p0 := strip p
  if p0.isZero then (RatConst.zero, [])
  else
    let c := content p0
    let p := monic (primitivePart p0)
    (c, factorMonic p [])
where
  factorMonic (p : Poly) (acc : List Poly) : List Poly :=
    let p := monic (strip p)
    if p.isZero || p.isOne || p.deg ≤ 0 then acc
    else if p.deg == 1 then monic p :: acc
    else
      match findLinear p with
      | some (lin, rest) => factorMonic rest (monic lin :: acc)
      | none => monic p :: acc

  findLinear (p : Poly) : Option (Poly × Poly) :=
    let cands := rationalRootCandidates p
    Id.run do
      for r in cands do
        if (eval p r).isZero then
          let lin : Poly := ⟨#[RatConst.neg r, RatConst.one]⟩
          match exactDiv p lin with
          | some rest => return some (lin, rest)
          | none => pure ()
      pure none

/-- Convert polynomial to `Expr` in variable `v`. -/
def toExpr (p : Poly) (v : String) : Expr :=
  let p := strip p
  if p.isZero then Expr.zero
  else
    Id.run do
      let mut terms : List Expr := []
      for i in [:p.coeffs.size] do
        let c := p.coeffs[i]!
        if !c.isZero then
          let term :=
            if i == 0 then Expr.const c
            else if i == 1 then
              if c.isOne then Expr.var v
              else Expr.mul (Expr.const c) (Expr.var v)
            else
              let xp := Expr.pow (Expr.var v) (Expr.ofInt i)
              if c.isOne then xp else Expr.mul (Expr.const c) xp
          terms := term :: terms
      -- sum terms (high degree first for pretty print)
      match terms with
      | [] => pure Expr.zero
      | t :: ts => pure (ts.foldl Expr.add t)

/-- Build poly from sparse terms `(coeff, degree)`. -/
def ofTerms (terms : List (RatConst × Nat)) : Poly :=
  terms.foldl (fun p (c, d) => add p (scale c (Xpow d))) zero

end Poly

end Taschenrechner
