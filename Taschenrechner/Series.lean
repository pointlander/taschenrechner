/-
  Taylor / Maclaurin / Laurent series and truncated series arithmetic.

  * `taylor f v a n` = ∑_{k=0}^{n} f^{(k)}(a)/k! · (v−a)^k
  * `laurent f v a n` = principal + regular part through O((v−a)^n)
  * Truncated series add/mul (and series of products/sums of functions)
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Eval
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Normal
import Taschenrechner.Limit

namespace Taschenrechner

open Expr

/-- `n!` as a natural number. -/
def natFactorial : Nat → Nat
  | 0 => 1
  | n'+1 => (n'+1) * natFactorial n'

/-- `n!` as an expression constant. -/
def factorialExpr (n : Nat) : Expr :=
  Expr.ofNat (natFactorial n)

/--
  Taylor polynomial of `f` in free variable `v`, expanded about `a`,
  of degree at most `n`.
-/
def taylor (f : Expr) (v : String) (a : Expr) (n : Nat) : Expr :=
  Id.run do
    let mut acc : Expr := zero
    let mut dk : Expr := simplify f
    for k in [0:n+1] do
      let ck := evalAtOrSimplify dk v a
      let term : Expr :=
        if k == 0 then ck
        else
          let powTerm :=
            if a == zero then
              if k == 1 then var v else pow (var v) (ofNat k)
            else
              let u := sub (var v) a
              if k == 1 then u else pow u (ofNat k)
          mul (div ck (factorialExpr k)) powTerm
      acc := add acc term
      dk := diff dk v
    pure (simplify acc)

/-- Maclaurin series: Taylor about 0. -/
def maclaurin (f : Expr) (v : String) (n : Nat) : Expr :=
  taylor f v zero n

/-- Convenience: Taylor about 0 in `"x"`. -/
def series (f : Expr) (n : Nat) (v : String := "x") : Expr :=
  maclaurin f v n

/-! ### Truncated Laurent / power series -/

/--
  Truncated series `∑_{k=0}^{m-1} c[k] · u^{offset+k}`.

  * `offset = 0` — ordinary power series
  * `offset < 0` — Laurent (pole of order `−offset` if `c[0] ≠ 0`)
-/
structure TruncSeries where
  offset : Int
  coeffs : Array Expr
  deriving Repr, Inhabited

namespace TruncSeries

def empty : TruncSeries := ⟨0, #[]⟩

def ofConst (c : Expr) : TruncSeries :=
  if simplify c == zero then empty else ⟨0, #[simplify c]⟩

def length (s : TruncSeries) : Nat := s.coeffs.size

/-- Highest power present: offset + length − 1 (or none if empty). -/
def maxPower (s : TruncSeries) : Option Int :=
  if s.coeffs.isEmpty then none
  else some (s.offset + (s.coeffs.size : Int) - 1)

def coeff (s : TruncSeries) (k : Int) : Expr :=
  let i := k - s.offset
  if i < 0 then zero
  else
    let i := i.toNat
    if i < s.coeffs.size then s.coeffs[i]! else zero

/-- Trim leading/trailing zero coefficients (keep mathematical offset). -/
def strip (s : TruncSeries) : TruncSeries :=
  if s.coeffs.isEmpty then empty
  else
    Id.run do
      let mut lo : Nat := 0
      let mut hi : Nat := s.coeffs.size
      while lo < hi && simplify s.coeffs[lo]! == zero do
        lo := lo + 1
      while hi > lo && simplify s.coeffs[hi - 1]! == zero do
        hi := hi - 1
      if lo >= hi then pure empty
      else
        let mut cs : Array Expr := Array.empty
        for i in [lo:hi] do
          cs := cs.push (simplify s.coeffs[i]!)
        pure ⟨s.offset + (lo : Int), cs⟩

/-- Truncate so only powers ≤ `maxDeg` are kept (relative to u^0). -/
def truncate (s : TruncSeries) (maxDeg : Int) : TruncSeries :=
  if s.coeffs.isEmpty then empty
  else
    Id.run do
      let mut cs : Array Expr := Array.empty
      for i in [:s.coeffs.size] do
        let pow := s.offset + (i : Int)
        if pow ≤ maxDeg then
          cs := cs.push s.coeffs[i]!
      pure (strip ⟨s.offset, cs⟩)

/-- Pad/align two series to a common offset and length up to maxDeg. -/
def align (a b : TruncSeries) (maxDeg : Int) : TruncSeries × TruncSeries :=
  let lo :=
    match a.coeffs.isEmpty, b.coeffs.isEmpty with
    | true, true => (0 : Int)
    | true, false => b.offset
    | false, true => a.offset
    | false, false => min a.offset b.offset
  let hi := maxDeg
  let len :=
    if hi < lo then 0 else (hi - lo + 1).toNat
  let build (s : TruncSeries) : TruncSeries :=
    Id.run do
      let mut cs : Array Expr := Array.replicate len zero
      for i in [:s.coeffs.size] do
        let p := s.offset + (i : Int)
        if p ≥ lo && p ≤ hi then
          let j := (p - lo).toNat
          if j < len then cs := cs.set! j (simplify s.coeffs[i]!)
      pure ⟨lo, cs⟩
  (build a, build b)

def add (a b : TruncSeries) (maxDeg : Int := 16) : TruncSeries :=
  let (a, b) := align a b maxDeg
  Id.run do
    let mut cs : Array Expr := Array.empty
    for i in [:a.coeffs.size] do
      cs := cs.push (simplify (Expr.add a.coeffs[i]! b.coeffs[i]!))
    pure (strip (truncate ⟨a.offset, cs⟩ maxDeg))

def neg (s : TruncSeries) : TruncSeries :=
  ⟨s.offset, s.coeffs.map fun c => simplify (Expr.neg c)⟩

def sub (a b : TruncSeries) (maxDeg : Int := 16) : TruncSeries :=
  add a (neg b) maxDeg

def scale (c : Expr) (s : TruncSeries) : TruncSeries :=
  let c := simplify c
  if c == zero then empty
  else ⟨s.offset, s.coeffs.map fun ci => simplify (mul c ci)⟩

/-- Multiply truncated series; result powers up to `maxDeg`. -/
def mul (a b : TruncSeries) (maxDeg : Int := 16) : TruncSeries :=
  if a.coeffs.isEmpty || b.coeffs.isEmpty then empty
  else
    let off := a.offset + b.offset
    let maxLen :=
      -- powers from off to maxDeg
      if maxDeg < off then 0 else (maxDeg - off + 1).toNat
    Id.run do
      let mut cs : Array Expr := Array.replicate maxLen zero
      for i in [:a.coeffs.size] do
        for j in [:b.coeffs.size] do
          let p := a.offset + (i : Int) + b.offset + (j : Int)
          if p ≤ maxDeg && p ≥ off then
            let k := (p - off).toNat
            if k < maxLen then
              cs := cs.set! k (simplify (Expr.add cs[k]! (Expr.mul a.coeffs[i]! b.coeffs[j]!)))
      pure (strip ⟨off, cs⟩)

/--
  Multiplicative inverse of a series with nonzero constant term
  (valuation 0), truncated to powers ≤ `maxDeg`.
-/
def inv (s : TruncSeries) (maxDeg : Int := 16) : Option TruncSeries :=
  let s := strip s
  if s.coeffs.isEmpty then none
  else if s.offset != 0 then none  -- use Laurent path first
  else
    let a0 := simplify s.coeffs[0]!
    if a0 == zero then none
    else
      let inv0 : Option Expr :=
        match eval? a0 with
        | some c =>
          if c.isZero then none
          else match CplxConst.inv c with
            | some invC => some (const invC)
            | none => none
        | none =>
          let inv0 := simplify (Expr.div one a0)
          some inv0
      match inv0 with
      | none => none
      | some inv0 =>
        Id.run do
          let mut bs : Array Expr := #[inv0]
          let nMax := (if maxDeg < 0 then 0 else maxDeg.toNat) + 1
          for n in [1:nMax] do
            let mut sum : Expr := zero
            for k in [1:n+1] do
              let ak := if k < s.coeffs.size then s.coeffs[k]! else zero
              let bnk := if n - k < bs.size then bs[n - k]! else zero
              sum := simplify (Expr.add sum (Expr.mul ak bnk))
            let bn := simplify (Expr.neg (Expr.mul inv0 sum))
            bs := bs.push bn
          pure (some (strip ⟨0, bs⟩))

/-- Convert to an expression in free variable `u` (the local coordinate). -/
def toExpr (s : TruncSeries) (u : Expr) : Expr :=
  let s := strip s
  if s.coeffs.isEmpty then zero
  else
    Id.run do
      let mut acc : Expr := zero
      for i in [:s.coeffs.size] do
        let c := s.coeffs[i]!
        if simplify c != zero then
          let p := s.offset + (i : Int)
          let term :=
            if p == 0 then c
            else if p == 1 then Expr.mul c u
            else if p == -1 then Expr.div c u
            else if p > 1 then
              Expr.mul c (pow u (ofInt p))
            else
              -- p ≤ -2: c / u^{|p|}
              Expr.div c (pow u (ofInt (-p)))
          acc := Expr.add acc term
      pure (simplify acc)

/-- Express series in original variable `v` about center `a`. -/
def toExprAbout (s : TruncSeries) (v : String) (a : Expr) : Expr :=
  let u := if a == zero then var v else Expr.sub (var v) a
  toExpr s u

end TruncSeries

/-! ### Polynomial → series helpers -/

/-- Horner shift: `p(X + a)` as a polynomial in X. -/
def polyShift (p : Poly) (a : RatConst) : Poly :=
  let p := Poly.strip p
  if p.isZero then Poly.zero
  else
    -- Horner: acc = 0; for c from high degree down: acc = acc*(X+a) + c
    Id.run do
      let mut acc := Poly.zero
      let mut i := p.coeffs.size
      while i > 0 do
        i := i - 1
        let c := p.coeffs[i]!
        -- acc = acc * (X + a) + c
        let accXa := Poly.mul acc (Poly.add Poly.X (Poly.ofConst a))
        acc := Poly.add accXa (Poly.ofConst c)
      pure (Poly.strip acc)

/-- Poly → truncated series (offset 0) with rational coeffs as Expr. -/
def polyToSeries (p : Poly) (maxDeg : Nat) : TruncSeries :=
  let p := Poly.strip p
  Id.run do
    let mut cs : Array Expr := Array.empty
    for i in [:maxDeg + 1] do
      cs := cs.push (ofRat (Poly.coeff p i))
    pure (TruncSeries.strip ⟨0, cs⟩)

/-- Valuation: largest `k` such that `u^k` divides `p` (p ≠ 0). -/
def polyValuation (p : Poly) : Nat :=
  let p := Poly.strip p
  if p.isZero then 0
  else
    Id.run do
      let mut k : Nat := 0
      while k < p.coeffs.size && (Poly.coeff p k).isZero do
        k := k + 1
      pure k

/-- Drop the first `k` coefficients (divide by X^k). -/
def polyDivXpow (p : Poly) (k : Nat) : Poly :=
  let p := Poly.strip p
  if k == 0 then p
  else if k >= p.coeffs.size then Poly.zero
  else Poly.strip ⟨p.coeffs.extract k p.coeffs.size⟩

/--
  Laurent series of a rational function about rational point `a`,
  through powers ≤ `n` (may include negative powers).
-/
def laurentRational (r : RatFn) (a : RatConst) (n : Nat) : Option TruncSeries :=
  let r := RatFn.simplify r
  let numU := polyShift r.num a
  let denU := polyShift r.den a
  if denU.isZero then none
  else
    let vN := polyValuation numU
    let vD := polyValuation denU
    let numR := polyDivXpow numU vN
    let denR := polyDivXpow denU vD
    -- num/den = u^{vN−vD} · (numR/denR) with denR(0) ≠ 0
    let offset : Int := (vN : Int) - (vD : Int)
    -- Need series of numR/denR through degree n − offset (if offset negative, more terms)
    let needDeg : Nat :=
      -- powers from offset to n → length n - offset + 1 for the regular part
      let maxReg : Int := (n : Int) - offset
      if maxReg < 0 then 0 else maxReg.toNat
    let numS := polyToSeries numR needDeg
    let denS := polyToSeries denR needDeg
    match TruncSeries.inv denS needDeg with
    | none => none
    | some invDen =>
      let reg := TruncSeries.mul numS invDen needDeg
      -- Multiply by u^{offset}: shift offset
      let s : TruncSeries := ⟨reg.offset + offset, reg.coeffs⟩
      some (TruncSeries.truncate s n)

/--
  Laurent expansion of `f` about `a` through degree `n` in `(v−a)`.

  * Rationals: exact series division after shift
  * Otherwise: if pole order `m` is known, Taylor-expand `(v−a)^m f` and divide;
    if regular, ordinary Taylor
-/
def laurent (f : Expr) (v : String) (a : Expr) (n : Nat) : Except String Expr :=
  let f := simplify f
  -- Rational path when a is rational
  match RatFn.ofExpr? f v, a with
  | some r, const c =>
    match CplxConst.toRat? c with
    | some q =>
      match laurentRational r q n with
      | some s => pure (TruncSeries.toExprAbout s v a)
      | none => throw "laurent: rational expansion failed (zero denominator?)"
    | none => throw "laurent: expansion point must be rational for rational functions"
  | some r, _ =>
    -- Try a = 0 only for non-const a? require rational a
    if a == zero then
      match laurentRational r RatConst.zero n with
      | some s => pure (TruncSeries.toExprAbout s v zero)
      | none => throw "laurent: rational expansion failed"
    else throw "laurent: expansion point must be a rational constant"
  | none, _ =>
    -- Analytic / elementary: use pole order if available
    let m :=
      match poleOrder? f v a with
      | some k => k
      | none => 0
    if m == 0 then
      pure (taylor f v a n)
    else
      -- g = (v−a)^m * f should be regular
      let u := sub (var v) a
      let g := simplify (mul (pow u (ofNat m)) f)
      let Tg := taylor g v a (n + m)
      -- Laurent = Tg / (v−a)^m
      pure (simplify (div Tg (pow u (ofNat m))))

/-- Laurent about 0. -/
def laurent0 (f : Expr) (v : String) (n : Nat) : Except String Expr :=
  laurent f v zero n

/-! ### Series arithmetic on functions -/

/--
  Truncated sum of series: `series(f,n) + series(g,n)` about `a`
  (computed via series objects, not by expanding the sum first).
-/
def seriesAdd (f g : Expr) (v : String) (a : Expr) (n : Nat) : Except String Expr := do
  let sf ← match laurent f v a n with
    | .ok e => pure e
    | .error msg => throw msg
  let sg ← match laurent g v a n with
    | .ok e => pure e
    | .error msg => throw msg
  -- Prefer arithmetic on series coeffs when both rational-laurent succeed
  match RatFn.ofExpr? (simplify f) v, RatFn.ofExpr? (simplify g) v, a with
  | some rf, some rg, const c =>
    match CplxConst.toRat? c with
    | some q =>
      match laurentRational rf q n, laurentRational rg q n with
      | some sf, some sg =>
        pure (TruncSeries.toExprAbout (TruncSeries.add sf sg n) v a)
      | _, _ => pure (simplify (add sf sg))
    | none => pure (simplify (add sf sg))
  | _, _, _ => pure (simplify (add sf sg))

/-- Drop powers of `(v−a)` higher than `n` in a polynomial-like expression. -/
def truncatePolyExpr (e : Expr) (v : String) (a : Expr) (n : Nat) : Expr :=
  let uName := "__u"
  let eU := simplify (subst e v (Expr.add (var uName) a))
  Id.run do
    let mut acc : Expr := zero
    let mut dk := eU
    for k in [0:n+1] do
      let ck := evalAtOrSimplify dk uName zero
      let term :=
        if k == 0 then ck
        else
          let u := if a == zero then var v else Expr.sub (var v) a
          let uk := if k == 1 then u else pow u (ofNat k)
          Expr.mul (Expr.div ck (factorialExpr k)) uk
      acc := Expr.add acc term
      dk := diff dk uName
    pure (simplify acc)

/-- Truncated product of series about `a` through degree `n`. -/
def seriesMul (f g : Expr) (v : String) (a : Expr) (n : Nat) : Except String Expr := do
  match RatFn.ofExpr? (simplify f) v, RatFn.ofExpr? (simplify g) v, a with
  | some rf, some rg, const c =>
    match CplxConst.toRat? c with
    | some q =>
      match laurentRational rf q n, laurentRational rg q n with
      | some sf, some sg =>
        pure (TruncSeries.toExprAbout (TruncSeries.mul sf sg n) v a)
      | _, _ =>
        laurent (Expr.mul f g) v a n
    | none => laurent (Expr.mul f g) v a n
  | _, _, _ =>
    let tf := taylor f v a n
    let tg := taylor g v a n
    pure (truncatePolyExpr (simplify (Expr.mul tf tg)) v a n)

/-- Convenience: series product about 0 in `x`. -/
def seriesMul0 (f g : Expr) (n : Nat) : Except String Expr :=
  seriesMul f g "x" zero n

def seriesAdd0 (f g : Expr) (n : Nat) : Except String Expr :=
  seriesAdd f g "x" zero n

end Taschenrechner
