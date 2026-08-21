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

/-- Laurent inverse: `u^k · r(u)` with `r(0) ≠ 0` → `u^{-k} / r(u)`. -/
def invFull (s : TruncSeries) (maxDeg : Int := 16) : Option TruncSeries :=
  let s := strip s
  if s.coeffs.isEmpty then none
  else if s.offset == 0 then inv s maxDeg
  else
    let r : TruncSeries := ⟨0, s.coeffs⟩
    let need : Int := maxDeg + s.offset
    match inv r (if need < 0 then maxDeg else need) with
    | none => none
    | some t => some (strip ⟨t.offset - s.offset, t.coeffs⟩)

/-- `s^n` truncated to `maxDeg`. -/
def powNat (s : TruncSeries) (n : Nat) (maxDeg : Int := 16) : TruncSeries :=
  match n with
  | 0 => ofConst 1
  | 1 => truncate s maxDeg
  | n'+1 => mul s (powNat s n' maxDeg) maxDeg

/--
  Compose Maclaurin `f` (offset 0, including zero coeffs) with `g` where `g(0)=0`
  (offset ≥ 1). Returns `f(g(u))`.
-/
def compose (f g : TruncSeries) (maxDeg : Int := 16) : TruncSeries :=
  let g := strip g
  if g.coeffs.isEmpty then
    if f.offset == 0 && f.coeffs.size > 0 then ofConst (simplify f.coeffs[0]!)
    else empty
  else if g.offset < 1 then empty
  else
    Id.run do
      let mut acc := empty
      let mut gk := ofConst 1
      for k in [:f.coeffs.size] do
        let fk := f.coeffs[k]!
        if simplify fk != zero then
          acc := add acc (scale fk gk) maxDeg
        gk := mul gk g maxDeg
      pure (strip acc)

/-- Split `c0 + h(u)` with `h(0)=0`. `none` if there is a pole (`offset < 0`). -/
def splitConst? (s : TruncSeries) : Option (Expr × TruncSeries) :=
  let s := strip s
  if s.coeffs.isEmpty then some (zero, empty)
  else if s.offset < 0 then none
  else if s.offset > 0 then some (zero, s)
  else
    let c0 := simplify s.coeffs[0]!
    let h : TruncSeries :=
      if s.coeffs.size ≤ 1 then empty
      else strip ⟨1, s.coeffs.extract 1 s.coeffs.size⟩
    some (c0, h)

end TruncSeries

/-! ### Elementary Maclaurin series (offset 0, zeros included) -/

/-- `(-1)^m` as an expression. -/
def signPow (m : Nat) : Expr :=
  if m % 2 == 0 then one else negOne

/-- Maclaurin coefficients `1/k!`. -/
def macExp (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.empty
    for k in [:maxDeg + 1] do
      cs := cs.push (ofRat ⟨1, natFactorial k⟩)
    pure ⟨0, cs⟩

def macSin (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.replicate (maxDeg + 1) zero
    let mut m : Nat := 0
    let mut k : Nat := 1
    while k ≤ maxDeg do
      cs := cs.set! k (mul (signPow m) (ofRat ⟨1, natFactorial k⟩))
      m := m + 1
      k := k + 2
    pure ⟨0, cs⟩

def macCos (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.replicate (maxDeg + 1) zero
    let mut m : Nat := 0
    let mut k : Nat := 0
    while k ≤ maxDeg do
      cs := cs.set! k (mul (signPow m) (ofRat ⟨1, natFactorial k⟩))
      m := m + 1
      k := k + 2
    pure ⟨0, cs⟩

def macSinh (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.replicate (maxDeg + 1) zero
    let mut k : Nat := 1
    while k ≤ maxDeg do
      cs := cs.set! k (ofRat ⟨1, natFactorial k⟩)
      k := k + 2
    pure ⟨0, cs⟩

def macCosh (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.replicate (maxDeg + 1) zero
    let mut k : Nat := 0
    while k ≤ maxDeg do
      cs := cs.set! k (ofRat ⟨1, natFactorial k⟩)
      k := k + 2
    pure ⟨0, cs⟩

/-- `ln(1+w) = ∑_{k≥1} (-1)^{k+1} w^k / k`. -/
def macLn1p (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.replicate (maxDeg + 1) zero
    for k in [1:maxDeg + 1] do
      let c := ofRat ⟨1, k⟩
      cs := cs.set! k (if k % 2 == 1 then c else neg c)
    pure ⟨0, cs⟩

/-- `√(1+w)` binomial series. -/
def macSqrt1p (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.replicate (maxDeg + 1) zero
    cs := cs.set! 0 one
    let mut bin : Expr := one
    for k in [1:maxDeg + 1] do
      -- binom(1/2, k) = binom(1/2, k-1) * (1/2 - (k-1)) / k
      let num := RatConst.sub ⟨1, 2⟩ (RatConst.ofInt (k - 1))
      bin := simplify (mul bin (div (ofRat num) (ofNat k)))
      cs := cs.set! k bin
    pure ⟨0, cs⟩

/-- `atan(w) = ∑ (-1)^m w^{2m+1} / (2m+1)`. -/
def macAtan (maxDeg : Nat) : TruncSeries :=
  Id.run do
    let mut cs : Array Expr := Array.replicate (maxDeg + 1) zero
    let mut m : Nat := 0
    let mut k : Nat := 1
    while k ≤ maxDeg do
      cs := cs.set! k (mul (signPow m) (ofRat ⟨1, k⟩))
      m := m + 1
      k := k + 2
    pure ⟨0, cs⟩

/-! ### Series of an elementary expression about `v = a` -/

def seriesMaxDeg : Nat := 8

/-- `sin(c0 + h)` via angle-addition when `h(0)=0`. -/
def seriesSinOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    if simplify c0 == zero then
      some (TruncSeries.compose (macSin maxDeg.toNat) h maxDeg)
    else
      let s0 := simplify (sin c0)
      let c0c := simplify (cos c0)
      let sh := TruncSeries.compose (macSin maxDeg.toNat) h maxDeg
      let ch := TruncSeries.compose (macCos maxDeg.toNat) h maxDeg
      -- sin(c0) cos(h) + cos(c0) sin(h)
      some (TruncSeries.add (TruncSeries.scale s0 ch) (TruncSeries.scale c0c sh) maxDeg)

def seriesCosOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    if simplify c0 == zero then
      some (TruncSeries.compose (macCos maxDeg.toNat) h maxDeg)
    else
      let s0 := simplify (sin c0)
      let c0c := simplify (cos c0)
      let sh := TruncSeries.compose (macSin maxDeg.toNat) h maxDeg
      let ch := TruncSeries.compose (macCos maxDeg.toNat) h maxDeg
      -- cos(c0) cos(h) − sin(c0) sin(h)
      some (TruncSeries.sub (TruncSeries.scale c0c ch) (TruncSeries.scale s0 sh) maxDeg)

def seriesExpOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    let eh := TruncSeries.compose (macExp maxDeg.toNat) h maxDeg
    if simplify c0 == zero then some eh
    else some (TruncSeries.scale (simplify (exp c0)) eh)

def seriesSinhOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    if simplify c0 == zero then
      some (TruncSeries.compose (macSinh maxDeg.toNat) h maxDeg)
    else none

def seriesCoshOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    if simplify c0 == zero then
      some (TruncSeries.compose (macCosh maxDeg.toNat) h maxDeg)
    else none

/-- `ln(inner)` when the constant term is a nonzero constant. -/
def seriesLnOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    if simplify c0 == zero then none
    else
      let w := TruncSeries.scale (simplify (div one c0)) h
      let ln1 := TruncSeries.compose (macLn1p maxDeg.toNat) w maxDeg
      some (TruncSeries.add (TruncSeries.ofConst (simplify (ln c0))) ln1 maxDeg)

/-- `√(inner)` when the constant term is a positive constant. -/
def seriesSqrtOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    if simplify c0 == zero then none
    else
      match eval? c0 with
      | some c =>
        match CplxConst.toRat? c with
        | some q =>
          if q.num ≤ 0 then none
          else
            let w := TruncSeries.scale (simplify (div one c0)) h
            let s1 := TruncSeries.compose (macSqrt1p maxDeg.toNat) w maxDeg
            some (TruncSeries.scale (simplify (sqrt c0)) s1)
        | none => none
      | none =>
        -- symbolic positive constant (e.g. √2): still try binomial
        let w := TruncSeries.scale (simplify (div one c0)) h
        let s1 := TruncSeries.compose (macSqrt1p maxDeg.toNat) w maxDeg
        some (TruncSeries.scale (simplify (sqrt c0)) s1)

def seriesAtanOf (inner : TruncSeries) (maxDeg : Int) : Option TruncSeries :=
  match TruncSeries.splitConst? inner with
  | none => none
  | some (c0, h) =>
    if simplify c0 == zero then
      some (TruncSeries.compose (macAtan maxDeg.toNat) h maxDeg)
    else none

/--
  Truncated Laurent/Taylor series of an elementary `e` in the local
  coordinate `u = v − a`, through degree `maxDeg`.
-/
partial def seriesAbout (e : Expr) (v : String) (a : Expr) (maxDeg : Nat := seriesMaxDeg) :
    Option TruncSeries :=
  let D : Int := maxDeg
  let e := simplify e
  if !dependsOn e v then some (TruncSeries.ofConst e)
  else
    match e with
    | const c => some (TruncSeries.ofConst (const c))
    | var name =>
      if name != v then some (TruncSeries.ofConst e)
      else
        -- v = a + u
        if simplify a == zero then some ⟨1, #[one]⟩
        else some ⟨0, #[simplify a, one]⟩
    | add p q =>
      match seriesAbout p v a maxDeg, seriesAbout q v a maxDeg with
      | some sp, some sq => some (TruncSeries.add sp sq D)
      | _, _ => none
    | mul p q =>
      match seriesAbout p v a maxDeg, seriesAbout q v a maxDeg with
      | some sp, some sq => some (TruncSeries.mul sp sq D)
      | _, _ => none
    | pow base expn =>
      match expn with
      | const r =>
        match CplxConst.toRat? r with
        | none => none
        | some q =>
          match seriesAbout base v a maxDeg with
          | none => none
          | some sb =>
            if q.den == 1 then
              if q.num ≥ 0 then some (TruncSeries.powNat sb q.num.toNat D)
              else TruncSeries.invFull (TruncSeries.powNat sb q.num.natAbs D) D
            else if q == ⟨1, 2⟩ then seriesSqrtOf sb D
            else if q == ⟨-1, 2⟩ then
              match seriesSqrtOf sb D with
              | some s => TruncSeries.invFull s D
              | none => none
            else
              -- a^q = exp(q ln a)
              match seriesLnOf sb D with
              | none => none
              | some sl =>
                seriesExpOf (TruncSeries.scale (ofRat q) sl) D
      | _ =>
        -- general power: exp(expn * ln base)
        match seriesAbout base v a maxDeg, seriesAbout expn v a maxDeg with
        | some sb, some se =>
          match seriesLnOf sb D with
          | none => none
          | some sl => seriesExpOf (TruncSeries.mul se sl D) D
        | _, _ => none
    | sin p =>
      match seriesAbout p v a maxDeg with
      | some s => seriesSinOf s D
      | none => none
    | cos p =>
      match seriesAbout p v a maxDeg with
      | some s => seriesCosOf s D
      | none => none
    | tan p =>
      match seriesAbout p v a maxDeg with
      | none => none
      | some s =>
        match seriesSinOf s D, seriesCosOf s D with
        | some ss, some sc =>
          match TruncSeries.invFull sc D with
          | some invc => some (TruncSeries.mul ss invc D)
          | none => none
        | _, _ => none
    | exp p =>
      match seriesAbout p v a maxDeg with
      | some s => seriesExpOf s D
      | none => none
    | ln p =>
      match seriesAbout p v a maxDeg with
      | some s => seriesLnOf s D
      | none => none
    | sinh p =>
      match seriesAbout p v a maxDeg with
      | some s => seriesSinhOf s D
      | none => none
    | cosh p =>
      match seriesAbout p v a maxDeg with
      | some s => seriesCoshOf s D
      | none => none
    | tanh p =>
      match seriesAbout p v a maxDeg with
      | none => none
      | some s =>
        match seriesSinhOf s D, seriesCoshOf s D with
        | some ss, some sc =>
          match TruncSeries.invFull sc D with
          | some invc => some (TruncSeries.mul ss invc D)
          | none => none
        | _, _ => none
    | atan p =>
      match seriesAbout p v a maxDeg with
      | some s => seriesAtanOf s D
      | none => none
    | sec p =>
      match seriesAbout p v a maxDeg with
      | none => none
      | some s =>
        match seriesCosOf s D with
        | some sc => TruncSeries.invFull sc D
        | none => none
    | csc p =>
      match seriesAbout p v a maxDeg with
      | none => none
      | some s =>
        match seriesSinOf s D with
        | some ss => TruncSeries.invFull ss D
        | none => none
    | cot p =>
      match seriesAbout p v a maxDeg with
      | none => none
      | some s =>
        match seriesCosOf s D, seriesSinOf s D with
        | some sc, some ss =>
          match TruncSeries.invFull ss D with
          | some invs => some (TruncSeries.mul sc invs D)
          | none => none
        | _, _ => none
    | _ => none

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
    -- Non-rational elementary: ordinary Taylor (poleOrder needs a rational).
    pure (taylor f v a n)

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
