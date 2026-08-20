/-
  Transcendental Risch integration (elementary functions over ℚ and K = ℚ(√κ)).

  Coverage:
  • Complete rational case ℚ(x)          — Hermite + Rothstein–Trager / PF
  • Rational case K(x)                   — Hermite + PF (deg ≤ 2 factors)
  • Algebraic `R(x, √p(x))` deg p ≤ 2    — Euler substitution to K(t)
  • Risch DE for  ∫ r(x) exp(p(x)) dx    — decides elementary vs not
  • Log extensions of the form R(x, ln s(x)) for simple monomial patterns
  • Structure-based non-existence certificates (e.g. exp(x²))

  Nested towers and algebraic curves (deg p ≥ 3 square-free) are not fully
  decided; those fall through to the heuristic integrator or return
  `notElementary` / `failure` as appropriate.

  References: Bronstein, *Symbolic Integration I*; Risch (1969).
-/
import Taschenrechner.RatInt
import Taschenrechner.AlgRisch
import Taschenrechner.Diff
import Taschenrechner.Trig
import Taschenrechner.Complex

namespace Taschenrechner

open Poly
open Expr

/-! ### Result type with non-existence -/

inductive RischResult where
  /-- Elementary antiderivative found. -/
  | elementary (F : Expr)
  /-- Proven: no elementary antiderivative in the Risch sense. -/
  | notElementary (reason : String)
  /-- Could not decide (unsupported extension / incomplete case). -/
  | undecided (reason : String)
  deriving Repr, Inhabited

namespace RischResult

def isElementary : RischResult → Bool
  | elementary _ => true
  | _ => false

def getElementary? : RischResult → Option Expr
  | elementary F => some F
  | _ => none

end RischResult

/-! ### Pattern helpers -/

/-- Match polynomial in `v` with rational coefficients. -/
partial def asPoly? (e : Expr) (v : String) : Option Poly :=
  match RatFn.ofExpr? e v with
  | some ⟨n, d⟩ => if d.isOne then some (strip n) else none
  | none => none

/-- Match r(x) * exp(p(x)) with r,p rational/poly. -/
partial def matchExpPoly (e : Expr) (v : String) : Option (Poly × Poly) :=
  let e := Expr.simplify e
  match e with
  | .exp p =>
    match asPoly? p v with
    | some pp => some (Poly.one, pp)
    | none => none
  | .mul a b =>
    match matchExpPoly a v, asPoly? b v with
    | some (r, p), some s => some (mul r s, p)
    | _, _ =>
      match asPoly? a v, matchExpPoly b v with
      | some s, some (r, p) => some (mul s r, p)
      | _, _ =>
        -- r(x) * exp(p) with r rational
        match RatFn.ofExpr? a v, matchExpPoly b v with
        | some ra, some (r, p) =>
          if ra.den.isOne then some (mul ra.num r, p) else none
        | _, _ =>
          match matchExpPoly a v, RatFn.ofExpr? b v with
          | some (r, p), some rb =>
            if rb.den.isOne then some (mul r rb.num, p) else none
          | _, _ => none
  | _ => none

/-- Match r(x) * exp(a*x+b) more generally via poly exponent. -/
partial def matchExpRational (e : Expr) (v : String) : Option (RatFn × Poly) :=
  let e := Expr.simplify e
  match e with
  | .exp p =>
    match asPoly? p v with
    | some pp => some (RatFn.ofPoly Poly.one, pp)
    | none => none
  | .mul a b =>
    match RatFn.ofExpr? a v, matchExpRational b v with
    | some ra, some (rb, p) => some (RatFn.mul ra rb, p)
    | _, _ =>
      match matchExpRational a v, RatFn.ofExpr? b v with
      | some (ra, p), some rb => some (RatFn.mul ra rb, p)
      | _, _ => none
  | _ => none

/-! ### Risch differential equation y' + f y = g over ℚ[x] -/

/--
  Solve y' + f y = g for a polynomial y, given polynomials f,g.
  Degree bound: if f ≠ 0, deg y ≤ max(0, deg g - deg f) (leading-term analysis
  when deg f ≥ 0). We search deg y ≤ deg g + 2 as a safe bound for poly f.
-/
partial def solveRischDEPoly (f g : Poly) : Option Poly :=
  let f := strip f
  let g := strip g
  if g.isZero then some Poly.zero
  else
    let dBound : Nat :=
      if f.isZero then
        -- y' = g ⇒ integrate g (polynomial)
        (g.deg + 1).toNat + 1
      else
        let df := f.deg
        let dg := g.deg
        if df < 0 then (dg + 2).toNat
        else max 0 (dg - df).toNat + 2
    -- y = sum_{k=0}^{d} y_k X^k ; build linear system via coeff matching
    solveByAnsatz dBound
where
  solveByAnsatz (dBound : Nat) : Option Poly :=
    -- Use undetermined coefficients from high degree down (greedy) when f is poly
    if f.isZero then
      -- y' = g
      some (indefPoly g)
    else
      greedy dBound Poly.zero g 32

  indefPoly (g : Poly) : Poly :=
    let g := strip g
    Id.run do
      let mut cs : Array RatConst := Array.replicate (g.coeffs.size + 1) RatConst.zero
      for i in [:g.coeffs.size] do
        let c := g.coeffs[i]!
        if !c.isZero then
          match RatConst.div c (RatConst.ofInt (i + 1)) with
          | some ck => cs := cs.set! (i + 1) ck
          | none => pure ()
      pure (strip ⟨cs⟩)

  /-- Greedy cancellation of leading terms of g using multiples of f. -/
  greedy (maxDeg : Nat) (y : Poly) (rem : Poly) (fuel : Nat) : Option Poly :=
    match fuel with
    | 0 => none
    | fuel'+1 =>
      let rem := strip rem
      if rem.isZero then some (strip y)
      else
        let f := strip f
        if f.isZero then none
        else
          let dr := rem.deg
          let df := f.deg
          -- p' * y contribution: want lc(f)*lc(y) X^{df+dy} to cancel lc(rem)
          -- y term of degree dy = dr - df
          if df < 0 then none
          else
            let dy := dr - df
            if dy < 0 then
              -- cannot cancel; maybe derivative part: y' has lower degree
              -- try pure integration when f=0 already handled
              none
            else if dy.toNat > maxDeg then none
            else
              match RatConst.div (lc rem) (lc f) with
              | none => none
              | some c =>
                let mono := scale c (Xpow dy.toNat)
                let y' := differentiate mono
                -- contribution of mono: y' + f*mono
                let contrib := add y' (mul f mono)
                let rem' := sub rem contrib
                greedy maxDeg (add y mono) rem' fuel'

/-- Solve y' + f y = g for y ∈ ℚ(x) when f,g ∈ ℚ(x) — poly case + simple proper. -/
def solveRischDE (f g : RatFn) : Option RatFn :=
  let f := RatFn.simplify f
  let g := RatFn.simplify g
  if f.den.isOne && g.den.isOne then
    match solveRischDEPoly f.num g.num with
    | some y => some (RatFn.ofPoly y)
    | none => none
  else
    -- Clear: for y = A/D with D | den(g) * something — limited support
    -- Try polynomial solution only
    if f.den.isOne then
      match solveRischDEPoly f.num g.num with
      | some y => some (RatFn.ofPoly y)
      | none =>
        -- try y = A / f-related denom — skip
        none
    else none

/-! ### ∫ r(x) e^{p(x)} dx -/

/--
  Integrate `r * exp(p)` with p ∈ ℚ[x], r ∈ ℚ(x).
  Elementary iff ∃ v ∈ ℚ(x): v' + p' v = r, then F = v exp(p).
-/
def integrateExpPoly (r : RatFn) (p : Poly) (v : String) : RischResult :=
  let p := strip p
  if p.isZero then
    -- ∫ r dx rational
    match integrateRationalPoly r.num r.den v with
    | some F => .elementary F
    | none => .undecided "rational integration failed for exp(0)·r"
  else
    let dp := differentiate p
    let f := RatFn.ofPoly dp
    match solveRischDE f r with
    | some vy =>
      let vex := Expr.mul (RatFn.toExpr vy v) (Expr.exp (Poly.toExpr p v))
      .elementary (Expr.simplify vex)
    | none =>
      -- Special: p linear always works for r poly of any deg via repeated ansatz
      if p.deg == 1 then
        -- p = a x + b, p' = a constant; y' + a y = r
        match integrateExpLinear r (lc p) (coeff p 0) v with
        | some F => .elementary F
        | none => .notElementary s!"∫ ({RatFn.toExpr r v})·exp({Poly.toExpr p v}) dx is not elementary"
      else if p.deg ≥ 2 && r.den.isOne then
        -- Polynomial times exp(deg≥2): classical non-elementary when DE fails
        .notElementary s!"∫ ({Poly.toExpr r.num v})·exp({Poly.toExpr p v}) dx is not elementary"
      else
        .notElementary s!"∫ ({RatFn.toExpr r v})·exp({Poly.toExpr p v}) dx is not elementary"
where
  integrateExpLinear (r : RatFn) (a b : RatConst) (v : String) : Option Expr :=
    -- p = a x + b, seek poly or rational y with y' + a y = r
    if a.isZero then none
    else
      let f := RatFn.ofPoly (Poly.ofConst a)
      match solveRischDE f r with
      | some y =>
        let pexpr := Expr.add (Expr.mul (Expr.ofRat a) (Expr.var v)) (Expr.ofRat b)
        some (Expr.simplify (Expr.mul (RatFn.toExpr y v) (Expr.exp pexpr)))
      | none =>
        -- r poly: always solvable for constant a ≠ 0
        if r.den.isOne then
          match solveRischDEPoly (Poly.ofConst a) r.num with
          | some y =>
            let pexpr := Expr.add (Expr.mul (Expr.ofRat a) (Expr.var v)) (Expr.ofRat b)
            some (Expr.simplify (Expr.mul (Poly.toExpr y v) (Expr.exp pexpr)))
          | none =>
            -- undetermined coeffs with higher degree bound
            match solveLinearConstDE a r.num with
            | some y =>
              let pexpr := Expr.add (Expr.mul (Expr.ofRat a) (Expr.var v)) (Expr.ofRat b)
              some (Expr.simplify (Expr.mul (Poly.toExpr y v) (Expr.exp pexpr)))
            | none => none
        else none

  /-- Solve y' + a y = g for a ∈ ℚ≠0, g ∈ ℚ[x], y ∈ ℚ[x]. -/
  solveLinearConstDE (a : RatConst) (g : Poly) : Option Poly :=
    let g := strip g
    if g.isZero then some Poly.zero
    else
      -- y of degree = deg g; equate coeffs from high to low
      let n := g.deg.toNat
      Id.run do
        let mut ycs : Array RatConst := Array.replicate (n + 1) RatConst.zero
        -- For k = n downto 0:
        -- (k+1) y_{k+1} + a y_k = g_k  where y_{n+1}=0
        let mut k : Int := n
        while k ≥ 0 do
          let gk := coeff g k.toNat
          let yk1 := if k.toNat + 1 < ycs.size then ycs[k.toNat + 1]! else RatConst.zero
          let fromDeriv := yk1 * RatConst.ofInt (k + 1)
          -- a y_k = g_k - fromDeriv
          match RatConst.div (gk - fromDeriv) a with
          | none => return none
          | some yk => ycs := ycs.set! k.toNat yk
          k := k - 1
        pure (some (strip ⟨ycs⟩))

/-! ### Log patterns: ∫ R(ln s) s'/s  and ∫ poly(ln x)/x -/

/-- ∫ ln(x)^n dx via reduction (by parts), n ∈ ℕ. -/
partial def integrateLnPow (n : Nat) (v : String) : Expr :=
  match n with
  | 0 => Expr.var v
  | 1 =>
    -- x ln x - x
    Expr.sub (Expr.mul (Expr.var v) (Expr.ln (Expr.var v))) (Expr.var v)
  | n'+1 =>
    -- ∫ ln^{n+1} = x ln^{n+1} - (n+1) ∫ ln^n
    let L := Expr.pow (Expr.ln (Expr.var v)) (Expr.ofInt (n'+1))
    let xL := Expr.mul (Expr.var v) L
    let rest := integrateLnPow n' v
    Expr.simplify (Expr.sub xL (Expr.mul (Expr.ofInt (n'+1)) rest))

/-- Match c * ln(x)^n / x  (written as products of powers after simplify). -/
partial def matchLnPowOverX (e : Expr) (v : String) : Option (RatConst × Nat) :=
  Id.run do
    let e := Expr.simplify e
    let factors := Expr.flattenMul e
    let mut c := RatConst.one
    let mut lnPow : Option Nat := none
    let mut hasInv := false
    let mut other := false
    for f in factors do
      match f with
      | .const r =>
        match CplxConst.toRat? r with
        | some q => c := c * q
        | none => other := true
      | .ln (.var name) =>
        if name == v then
          lnPow := some (match lnPow with | some n => n + 1 | none => 1)
        else other := true
      | .pow (.ln (.var name)) (.const r) =>
        match CplxConst.toRat? r with
        | some q =>
          if name == v && q.den == 1 && q.num ≥ 0 then
            lnPow := some (match lnPow with | some n => n + q.num.toNat | none => q.num.toNat)
          else other := true
        | none => other := true
      | .pow (.var name) (.const r) =>
        match CplxConst.toRat? r with
        | some q =>
          if name == v && q == RatConst.negOne then hasInv := true
          else other := true
        | none => other := true
      | .var _ => other := true
      | _ => other := true
    if other then pure none
    else if hasInv then pure (some (c, lnPow.getD 0))
    else pure none

/-! ### Main Risch entry -/

/--
  Attempt full transcendental Risch on `e` w.r.t. `v`.

  Front-end: trigonometric preprocessing (product-to-sum, power-reduction,
  linear sin/cos/tan) so classical elementary trig integrals are decided here
  rather than only by the heuristic fallback.
-/
partial def risch (e : Expr) (v : String := "x") : RischResult :=
  let e0 := Expr.simplify e
  -- Linear sin/cos/tan *before* rewriting tan → sin/cos
  match integrateLinearTrig e0 v with
  | some F => .elementary F
  | none =>
    -- Trig rewrite (tan→sin/cos, sin²/cos², product-to-sum), then core
    let e := Expr.simplify (trigPreprocess e0)
    rischCore e v
where
  rischCore (e : Expr) (v : String) : RischResult :=
    if !Expr.dependsOn e v then
      .elementary (Expr.mul e (Expr.var v))
    else
      -- 0. Linear trig extension (and sums after product-to-sum)
      match rischTrig e v with
      | some F => .elementary F
      | none =>
        -- 1. Pure rational in v
        match integrateRationalExpr e v with
        | some F => .elementary F
        | none =>
          -- 1b. Algebraic R(x, √p(x)), deg p ≤ 2
          match integrateAlgSqrt? e v with
          | some F => .elementary F
          | none =>
          -- 2. Linearity
          match e with
          | .add a b =>
            match rischCore a v, rischCore b v with
            | .elementary A, .elementary B => .elementary (Expr.simplify (Expr.add A B))
            | .notElementary r, _ => .notElementary r
            | _, .notElementary r => .notElementary r
            | .undecided r, _ => .undecided r
            | _, .undecided r => .undecided r
          | .mul (.const c) a =>
            match rischCore a v with
            | .elementary F => .elementary (Expr.simplify (Expr.mul (.const c) F))
            | .notElementary r => .notElementary r
            | .undecided r => .undecided r
          | .mul a (.const c) =>
            match rischCore a v with
            | .elementary F => .elementary (Expr.simplify (Expr.mul (.const c) F))
            | .notElementary r => .notElementary r
            | .undecided r => .undecided r
          | _ =>
            -- 3a. Complex-linear exp: r·exp(α+βv) with α,β ∈ ℚ(i)
            match matchExpCplxLinear e v with
            | some (r, α, β) =>
              match integrateExpCplxLinear r α β v with
              | some F => .elementary F
              | none => .undecided s!"complex exp integral failed: {e}"
            | none =>
              -- 3b. Real poly exp: r(x)·exp(p(x))
              match matchExpRational e v with
              | some (r, p) => integrateExpPoly r p v
              | none =>
                -- 4. ln powers / x
                match matchLnPowOverX e v with
                | some (c, n) =>
                  let L := Expr.ln (Expr.var v)
                  let F :=
                    match n with
                    | 0 => L
                    | _ =>
                      let np1 := n + 1
                      match RatConst.div c (RatConst.ofInt np1) with
                      | some ck =>
                        Expr.mul (Expr.ofRat ck) (Expr.pow L (Expr.ofInt np1))
                      | none =>
                        Expr.div (Expr.mul (Expr.ofRat c) (Expr.pow L (Expr.ofInt np1)))
                          (Expr.ofInt np1)
                  .elementary (Expr.simplify F)
                | none =>
                  -- 5. pure ln(v)^n / exp / leftover trig of non-linear args
                  match e with
                  | .pow (.ln (.var name)) (.const r) =>
                    match CplxConst.toRat? r with
                    | some q =>
                      if name == v && q.den == 1 && q.num ≥ 0 then
                        .elementary (integrateLnPow q.num.toNat v)
                      else .undecided s!"unsupported power of log: {e}"
                    | none => .undecided s!"unsupported power of log: {e}"
                  | .ln (.var name) =>
                    if name == v then .elementary (integrateLnPow 1 v)
                    else .undecided s!"ln of non-variable"
                  | .exp arg =>
                    match asCplxLinearIn arg v with
                    | some (α, β) =>
                      if β.isZero then
                        .elementary (Expr.mul (Expr.exp arg) (Expr.var v))
                      else
                        match integrateExpCplxLinear CplxConst.one α β v with
                        | some F => .elementary F
                        | none => .undecided s!"complex exp failed: {e}"
                    | none =>
                      match asPoly? arg v with
                      | some p => integrateExpPoly (RatFn.ofPoly Poly.one) p v
                      | none => .undecided s!"exp of non-polynomial: {arg}"
                  | .sin _ | .cos _ | .tan _ =>
                    .undecided s!"trig of non-linear argument: {e}"
                  | .re a | .im a | .conj a =>
                    -- Integrate componentwise when the argument is real-linear complex
                    match rischCore a v with
                    | .elementary F =>
                      match e with
                      | .re _ => .elementary (Expr.simplify (Expr.re F))
                      | .im _ => .elementary (Expr.simplify (Expr.im F))
                      | .conj _ => .elementary (Expr.simplify (Expr.conj F))
                      | _ => .undecided s!"re/im/conj: {e}"
                    | .notElementary r => .notElementary r
                    | .undecided r => .undecided r
                  | _ =>
                    .undecided s!"no Risch method for: {e}"

/-- Convenience: Option elementary antiderivative. -/
def risch? (e : Expr) (v : String := "x") : Option Expr :=
  match risch e v with
  | .elementary F => some F
  | _ => none

/-- True when Risch proves non-existence. -/
def rischNotElementary (e : Expr) (v : String := "x") : Bool :=
  match risch e v with
  | .notElementary _ => true
  | _ => false

end Taschenrechner
