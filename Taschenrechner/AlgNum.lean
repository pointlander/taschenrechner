/-
  Algebraic numbers in a real multiquadratic field
  K = ℚ(√κ₁, √κ₂, …) with square-free kernels κᵢ.

  An element is stored uniquely as Σ cᵢ √κᵢ (cᵢ ∈ ℚ, κᵢ square-free).
  This is the coefficient field for `nf` in K(x), e.g. ℚ(√2)(x).
-/
import Taschenrechner.Expr

namespace Taschenrechner

/-! ### Square-free splitting -/

/-- `n = s² · κ` with `κ` square-free. -/
def splitSquareFree (n : Nat) : Nat × Nat :=
  if n == 0 then (0, 1)
  else
    Id.run do
      let mut s : Nat := 1
      let mut m : Nat := n
      let mut i : Nat := 2
      while i * i ≤ m do
        let i2 := i * i
        while m % i2 == 0 do
          m := m / i2
          s := s * i
        i := i + 1
      pure (s, m)

/-- Perfect rational square, if any. -/
def perfectSquareRat? (q : RatConst) : Option RatConst :=
  RatConst.nthRoot? (RatConst.normalize q) 2

/-! ### Algebraic numbers Σ c √κ -/

/-- One term `coeff · √kernel` (`kernel = 1` is rational). -/
structure AlgTerm where
  coeff  : RatConst
  kernel : Nat
  deriving Repr, Inhabited

/-- Element of a real multiquadratic field, terms sorted by kernel. -/
structure AlgNum where
  terms : List AlgTerm
  deriving Repr, Inhabited

namespace AlgNum

def zero : AlgNum := ⟨[]⟩
def one  : AlgNum := ⟨[⟨RatConst.one, 1⟩]⟩
def negOne : AlgNum := ⟨[⟨RatConst.negOne, 1⟩]⟩

def isZero (α : AlgNum) : Bool := α.terms.isEmpty
def isOne  (α : AlgNum) : Bool :=
  match α.terms with
  | [t] => t.kernel == 1 && t.coeff.isOne
  | _ => false

def ofRat (q : RatConst) : AlgNum :=
  let q := RatConst.normalize q
  if q.isZero then zero else ⟨[⟨q, 1⟩]⟩

def ofInt (n : Int) : AlgNum := ofRat (RatConst.ofInt n)
def ofNat (n : Nat) : AlgNum := ofInt n

def toRat? (α : AlgNum) : Option RatConst :=
  match α.terms with
  | [] => some RatConst.zero
  | [t] => if t.kernel == 1 then some t.coeff else none
  | _ => none

private def insertTerm (t : AlgTerm) : List AlgTerm → List AlgTerm
  | [] => if t.coeff.isZero then [] else [t]
  | t' :: rest =>
    if t.kernel == t'.kernel then
      let c := RatConst.normalize (t.coeff + t'.coeff)
      if c.isZero then rest else { t' with coeff := c } :: rest
    else if t.kernel < t'.kernel then
      if t.coeff.isZero then t' :: rest else { t with coeff := RatConst.normalize t.coeff } :: t' :: rest
    else t' :: insertTerm t rest

def normalize (α : AlgNum) : AlgNum :=
  ⟨α.terms.foldl (fun acc t => insertTerm t acc) []⟩

def add (α β : AlgNum) : AlgNum :=
  normalize ⟨α.terms ++ β.terms⟩

def neg (α : AlgNum) : AlgNum :=
  ⟨α.terms.map fun t => { t with coeff := RatConst.neg t.coeff }⟩

def sub (α β : AlgNum) : AlgNum := add α (neg β)

def scale (c : RatConst) (α : AlgNum) : AlgNum :=
  if c.isZero then zero
  else if c.isOne then α
  else normalize ⟨α.terms.map fun t => { t with coeff := t.coeff * c }⟩

/-- `√a · √b = s √κ` after absorbing squares. -/
def mulTerm (a b : AlgTerm) : AlgTerm :=
  let (s, κ) := splitSquareFree (a.kernel * b.kernel)
  ⟨a.coeff * b.coeff * RatConst.ofInt (s : Int), κ⟩

def mul (α β : AlgNum) : AlgNum :=
  Id.run do
    let mut acc : List AlgTerm := []
    for ta in α.terms do
      for tb in β.terms do
        acc := insertTerm (mulTerm ta tb) acc
    pure ⟨acc⟩

def powNat (α : AlgNum) : Nat → AlgNum
  | 0 => one
  | n'+1 => mul (powNat α n') α

/-- Split `α = A + B √d` (A, B free of the factor `d` in their kernels). -/
def splitOn (α : AlgNum) (d : Nat) : AlgNum × AlgNum :=
  if d ≤ 1 then (α, zero)
  else
    let rec go (ts : List AlgTerm) (a b : List AlgTerm) : AlgNum × AlgNum :=
      match ts with
      | [] => (normalize ⟨a⟩, normalize ⟨b⟩)
      | t :: rest =>
        if t.kernel % d == 0 then
          go rest a (⟨t.coeff, t.kernel / d⟩ :: b)
        else
          go rest (t :: a) b
    go α.terms [] []

/-- Smallest kernel strictly greater than 1, if any. -/
def minIrrKernel (α : AlgNum) : Option Nat :=
  α.terms.findSome? fun t => if t.kernel > 1 then some t.kernel else none

/-- Field inverse: `(a + b√d)⁻¹ = (a − b√d) / (a² − d b²)`. -/
partial def inv (α : AlgNum) : Option AlgNum :=
  let α := normalize α
  if α.isZero then none
  else
    match α.terms with
    | [] => none
    | [t] =>
      -- 1/(c √κ) = (1/(c κ)) √κ
      match RatConst.inv (t.coeff * RatConst.ofInt (t.kernel : Int)) with
      | none => none
      | some c => some ⟨[⟨c, t.kernel⟩]⟩
    | _ =>
      match minIrrKernel α with
      | none =>
        match toRat? α with
        | some q => RatConst.inv q |>.map ofRat
        | none => none
      | some d =>
        let (a, b) := splitOn α d
        let norm := sub (mul a a) (scale (RatConst.ofInt d) (mul b b))
        match inv norm with
        | none => none
        | some ninv =>
          let conj := sub a (mul b ⟨[⟨RatConst.one, d⟩]⟩)
          some (mul ninv conj)

def div (α β : AlgNum) : Option AlgNum :=
  match inv β with
  | some β' => some (mul α β')
  | none => none

def powInt (α : AlgNum) (n : Int) : Option AlgNum :=
  if n == 0 then some one
  else if α.isZero then
    if n > 0 then some zero else none
  else if n > 0 then some (powNat α n.toNat)
  else
    match inv α with
    | none => none
    | some α' => some (powNat α' n.natAbs)

def beq (α β : AlgNum) : Bool :=
  let α := normalize α; let β := normalize β
  if α.terms.length != β.terms.length then false
  else
    Id.run do
      for p in α.terms.zip β.terms do
        if !(p.1.coeff == p.2.coeff && p.1.kernel == p.2.kernel) then
          return false
      pure true

instance : BEq AlgNum where beq := beq
instance : Add AlgNum where add := add
instance : Mul AlgNum where mul := mul
instance : Neg AlgNum where neg := neg
instance : Sub AlgNum where sub := sub
instance : OfNat AlgNum n where ofNat := ofNat n

/-- Principal square root of a nonnegative rational, in the field. -/
def ofSqrtRat? (q : RatConst) : Option AlgNum :=
  let q := RatConst.normalize q
  if q.isZero then some zero
  else if q.num < 0 then none
  else
    -- √(n/d) = √(n d) / d
    let nd := q.num.natAbs * q.den
    let (s, κ) := splitSquareFree nd
    some (scale (RatConst.normalize ⟨(s : Int), q.den⟩) ⟨[⟨RatConst.one, κ⟩]⟩)

/-- Denest `√(a + b √d)` when `a² − b² d` is a rational square. -/
def denestQuadratic? (a b : RatConst) (d : Nat) : Option AlgNum :=
  if d ≤ 1 || b.isZero then
    if b.isZero then ofSqrtRat? a else none
  else
    let disc := a * a - b * b * RatConst.ofInt d
    match perfectSquareRat? disc with
    | none => none
    | some s =>
      -- √(a + b√d) = √x + sign(b) √y,  x,y = (a ± s)/2
      let half : RatConst := ⟨1, 2⟩
      let x := (a + s) * half
      let y := (a - s) * half
      if x.num < 0 || y.num < 0 then
        -- try the other sign of s
        let s := RatConst.neg s
        let x := (a + s) * half
        let y := (a - s) * half
        if x.num < 0 || y.num < 0 then none
        else
          match ofSqrtRat? x, ofSqrtRat? y with
          | some sx, some sy =>
            some (add sx (if b.num < 0 then neg sy else sy))
          | _, _ => none
      else
        match ofSqrtRat? x, ofSqrtRat? y with
        | some sx, some sy =>
          some (add sx (if b.num < 0 then neg sy else sy))
        | _, _ => none

/-- Square root in the field, when it stays multiquadratic. -/
def sqrt? (α : AlgNum) : Option AlgNum :=
  let α := normalize α
  match α.terms with
  | [] => some zero
  | [t] =>
    if t.kernel == 1 then ofSqrtRat? t.coeff
    else
      -- √(c √κ) is nested (4th-root) unless c is a square times κ⁰
      none
  | [t1, t2] =>
    -- a + b√d  (kernels 1 and d, or two irrational kernels)
    if t1.kernel == 1 then
      denestQuadratic? t1.coeff t2.coeff t2.kernel
    else none
  | _ => none

/-- Rebuild a principal `√n` expression. -/
def sqrtNat (n : Nat) : AlgNum :=
  if n == 0 then zero
  else
    let (s, κ) := splitSquareFree n
    scale (RatConst.ofInt s) ⟨[⟨RatConst.one, κ⟩]⟩

/-- Convert to an `Expr` (`√κ` as `pow κ (1/2)`). -/
def toExpr (α : AlgNum) : Expr :=
  let α := normalize α
  let termE (t : AlgTerm) : Expr :=
    let rad :=
      if t.kernel == 1 then Expr.one
      else Expr.pow (Expr.ofNat t.kernel) (Expr.ofRat ⟨1, 2⟩)
    if t.kernel == 1 then Expr.ofRat t.coeff
    else if t.coeff.isOne then rad
    else if t.coeff.isNegOne then Expr.neg rad
    else Expr.mul (Expr.ofRat t.coeff) rad
  match α.terms with
  | [] => Expr.zero
  | t :: ts => ts.foldl (fun acc t => Expr.add acc (termE t)) (termE t)

/-- Recognise a closed real multiquadratic constant. -/
partial def ofExpr? : Expr → Option AlgNum
  | .const c =>
    match CplxConst.toRat? c with
    | some q => some (ofRat q)
    | none => none
  | .add a b =>
    match ofExpr? a, ofExpr? b with
    | some α, some β => some (add α β)
    | _, _ => none
  | .mul a b =>
    match ofExpr? a, ofExpr? b with
    | some α, some β => some (mul α β)
    | _, _ => none
  | .pow base (.const r) =>
    match CplxConst.toRat? r with
    | none => none
    | some q =>
      if q == ⟨1, 2⟩ then
        match ofExpr? base with
        | some α => sqrt? α
        | none => none
      else if q == ⟨-1, 2⟩ then
        match ofExpr? base with
        | some α =>
          match sqrt? α with
          | some s => inv s
          | none => none
        | none => none
      else if q.den == 1 then
        match ofExpr? base with
        | some α => powInt α q.num
        | none => none
      else if q.den == 2 && q.num.natAbs != 1 then
        -- r = n/2 = n * (1/2):  α^{n/2} = (√α)^n
        match ofExpr? base with
        | some α =>
          match sqrt? α with
          | some s => powInt s q.num
          | none => none
        | none => none
      else none
  | .pow _ _ => none
  | .var _ | .sin _ | .cos _ | .tan _ | .sinh _ | .cosh _ | .tanh _
  | .exp _ | .ln _ | .atan _ | .asin _ | .acos _ | .sec _ | .csc _ | .cot _
  | .factorial _ | .gamma _ | .floor _ | .ite _ _ _ | .abs _ | .re _ | .im _ | .conj _
  | .eq _ _ | .lt _ _ | .le _ _ | .mat _ => none

/-- Fold a closed algebraic expression; leave everything else unchanged. -/
def foldExpr (e : Expr) : Expr :=
  match ofExpr? e with
  | some α => toExpr α
  | none => e

end AlgNum

/-! ### Polynomials over K = AlgNum -/

structure AlgPoly where
  coeffs : Array AlgNum
  deriving Repr, Inhabited

namespace AlgPoly

def zero : AlgPoly := ⟨#[]⟩
def one  : AlgPoly := ⟨#[AlgNum.one]⟩
def ofConst (c : AlgNum) : AlgPoly :=
  if c.isZero then zero else ⟨#[c]⟩
def X : AlgPoly := ⟨#[AlgNum.zero, AlgNum.one]⟩

def strip (p : AlgPoly) : AlgPoly :=
  Id.run do
    let mut cs := p.coeffs
    while cs.size > 0 && cs.back!.isZero do
      cs := cs.pop
    pure ⟨cs⟩

def deg (p : AlgPoly) : Int :=
  let p := strip p
  if p.coeffs.isEmpty then -1 else (p.coeffs.size : Int) - 1

def isZero (p : AlgPoly) : Bool := strip p |>.coeffs.isEmpty
def isOne (p : AlgPoly) : Bool :=
  let p := strip p
  p.coeffs.size == 1 && p.coeffs[0]!.isOne

def coeff (p : AlgPoly) (i : Nat) : AlgNum :=
  p.coeffs[i]?.getD AlgNum.zero

def lc (p : AlgPoly) : AlgNum :=
  let p := strip p
  if p.coeffs.isEmpty then AlgNum.zero else p.coeffs.back!

def add (a b : AlgPoly) : AlgPoly :=
  Id.run do
    let n := max a.coeffs.size b.coeffs.size
    let mut cs : Array AlgNum := Array.replicate n AlgNum.zero
    for i in [:n] do
      cs := cs.set! i (AlgNum.add (coeff a i) (coeff b i))
    pure (strip ⟨cs⟩)

def neg (p : AlgPoly) : AlgPoly := ⟨p.coeffs.map AlgNum.neg⟩
def sub (a b : AlgPoly) : AlgPoly := add a (neg b)

def scale (c : AlgNum) (p : AlgPoly) : AlgPoly :=
  if c.isZero then zero else ⟨p.coeffs.map (fun a => AlgNum.mul c a)⟩

def mul (a b : AlgPoly) : AlgPoly :=
  if a.isZero || b.isZero then zero
  else
    Id.run do
      let n := a.coeffs.size + b.coeffs.size - 1
      let mut cs : Array AlgNum := Array.replicate n AlgNum.zero
      for i in [:a.coeffs.size] do
        for j in [:b.coeffs.size] do
          let k := i + j
          cs := cs.set! k (AlgNum.add cs[k]! (AlgNum.mul a.coeffs[i]! b.coeffs[j]!))
      pure (strip ⟨cs⟩)

def Xpow (n : Nat) : AlgPoly :=
  if n == 0 then one
  else ⟨Array.replicate n AlgNum.zero |>.push AlgNum.one⟩

def powNat (p : AlgPoly) : Nat → AlgPoly
  | 0 => one
  | n'+1 => mul (powNat p n') p

partial def divMod (a b : AlgPoly) : AlgPoly × AlgPoly :=
  let b := strip b
  if b.isZero then (zero, strip a)
  else
    let lb := lc b
    let rec loop (q r : AlgPoly) (fuel : Nat) : AlgPoly × AlgPoly :=
      match fuel with
      | 0 => (strip q, strip r)
      | fuel'+1 =>
        let r := strip r
        if r.isZero || r.deg < b.deg then (strip q, r)
        else
          match AlgNum.div (lc r) lb with
          | none => (strip q, r)
          | some c =>
            let shift := (r.deg - b.deg).toNat
            let mono := scale c (Xpow shift)
            loop (add q mono) (sub r (mul mono b)) fuel'
    loop zero (strip a) 256

def modPoly (a b : AlgPoly) : AlgPoly := (divMod a b).2

def monic (p : AlgPoly) : AlgPoly :=
  let p := strip p
  if p.isZero then zero
  else
    match AlgNum.inv (lc p) with
    | none => p
    | some inv => scale inv p

partial def gcd (a b : AlgPoly) : AlgPoly :=
  let a := strip a; let b := strip b
  if b.isZero then monic a
  else if a.isZero then monic b
  else gcd b (modPoly a b)

def exactDiv (a b : AlgPoly) : Option AlgPoly :=
  if b.isZero then none
  else
    let (q, r) := divMod a b
    if r.isZero then some (strip q) else none

/-- Kernels appearing in any coefficient. -/
def kernels (p : AlgPoly) : List Nat :=
  p.coeffs.foldl (fun acc α =>
    α.terms.foldl (fun acc t =>
      if t.kernel > 1 && !acc.contains t.kernel then acc ++ [t.kernel] else acc) acc) []

/-- Coefficient of `√k` in `α`. -/
def ratPart (α : AlgNum) (k : Nat) : RatConst :=
  match α.terms.find? (fun t => t.kernel == k) with
  | some t => t.coeff
  | none => RatConst.zero

/-- Split `p = A + B √d` with A, B free of factor `d`. -/
def splitOn (p : AlgPoly) (d : Nat) : AlgPoly × AlgPoly :=
  Id.run do
    let mut a : Array AlgNum := Array.replicate p.coeffs.size AlgNum.zero
    let mut b : Array AlgNum := Array.replicate p.coeffs.size AlgNum.zero
    for i in [:p.coeffs.size] do
      let (ai, bi) := AlgNum.splitOn p.coeffs[i]! d
      a := a.set! i ai
      b := b.set! i bi
    pure (strip ⟨a⟩, strip ⟨b⟩)

/-- All distinct kernels across num/den (including 1). -/
def allKernels (p : AlgPoly) : List Nat :=
  p.coeffs.foldl (fun acc α =>
    α.terms.foldl (fun acc t =>
      if acc.contains t.kernel then acc else acc ++ [t.kernel]) acc) []

/-- Coordinate polynomial of kernel `k` (rational coeffs). -/
def coord (p : AlgPoly) (k : Nat) : Array RatConst :=
  p.coeffs.map (fun α => ratPart α k)

def toExpr (p : AlgPoly) (v : String) : Expr :=
  let p := strip p
  if p.isZero then Expr.zero
  else
    Id.run do
      let mut acc : Expr := Expr.zero
      for i in [:p.coeffs.size] do
        let c := p.coeffs[i]!
        if !c.isZero then
          let xp :=
            if i == 0 then Expr.one
            else if i == 1 then Expr.var v
            else Expr.pow (Expr.var v) (Expr.ofNat i)
          let term :=
            if i == 0 then AlgNum.toExpr c
            else if c.isOne then xp
            else Expr.mul (AlgNum.toExpr c) xp
          acc := if acc == Expr.zero then term else Expr.add acc term
      pure acc

end AlgPoly

/-! ### Rational functions over K -/

structure AlgRatFn where
  num : AlgPoly
  den : AlgPoly
  deriving Repr, Inhabited

namespace AlgRatFn

def zero : AlgRatFn := ⟨AlgPoly.zero, AlgPoly.one⟩
def ofPoly (p : AlgPoly) : AlgRatFn := ⟨p, AlgPoly.one⟩
def ofConst (c : AlgNum) : AlgRatFn := ofPoly (AlgPoly.ofConst c)

/-- Multiply num and den by the conjugate that eliminates kernel `d` from den. -/
def conjCancel (r : AlgRatFn) (d : Nat) : AlgRatFn :=
  if d ≤ 1 then r
  else
    let (n0, n1) := AlgPoly.splitOn r.num d
    let (d0, d1) := AlgPoly.splitOn r.den d
    -- (n0 + n1 √d)(d0 − d1 √d) / (d0² − d d1²)
    let sqrtD : AlgNum := ⟨[⟨RatConst.one, d⟩]⟩
    let dd : AlgNum := AlgNum.ofNat d
    let newN0 := AlgPoly.sub (AlgPoly.mul n0 d0) (AlgPoly.scale dd (AlgPoly.mul n1 d1))
    let newN1 := AlgPoly.sub (AlgPoly.mul n1 d0) (AlgPoly.mul n0 d1)
    -- newN = newN0 + newN1 √d
    let newN :=
      AlgPoly.add newN0 (AlgPoly.scale sqrtD newN1)
    let newD :=
      AlgPoly.sub (AlgPoly.mul d0 d0) (AlgPoly.scale dd (AlgPoly.mul d1 d1))
    ⟨newN, newD⟩

/-- Push every irrational kernel out of the denominator. -/
partial def rationalize (r : AlgRatFn) : AlgRatFn :=
  let ks := AlgPoly.kernels r.den
  match ks.mergeSort (· < ·) with
  | [] => r
  | d :: _ =>
    let r' := conjCancel r d
    if (AlgPoly.kernels r'.den).length < ks.length then rationalize r'
    else r'

/-- GCD of all rational coordinate polynomials of `p` (as primitive ℚ[x] via AlgPoly). -/
def contentGcd (p : AlgPoly) (d : AlgPoly) : AlgPoly :=
  let rec go (ks : List Nat) (g : AlgPoly) : AlgPoly :=
    match ks with
    | [] => g
    | k :: rest =>
      -- build the k-coordinate as an AlgPoly with rational terms
      let ck : AlgPoly :=
        ⟨p.coeffs.map fun α => AlgNum.ofRat (AlgPoly.ratPart α k)⟩
      go rest (AlgPoly.gcd g (AlgPoly.strip ck))
  let g0 := AlgPoly.strip d
  let ks := AlgPoly.allKernels p
  let g := go ks g0
  if g.isZero then AlgPoly.one else AlgPoly.monic g

def simplify (r : AlgRatFn) : AlgRatFn :=
  let r := { r with num := AlgPoly.strip r.num, den := AlgPoly.strip r.den }
  if r.num.isZero then zero
  else if r.den.isZero then r
  else
    let r := rationalize r
    let g := contentGcd r.num r.den
    let n := match AlgPoly.exactDiv r.num g with | some q => q | none => r.num
    let d := match AlgPoly.exactDiv r.den g with | some q => q | none => r.den
    -- make den monic
    match AlgNum.inv (AlgPoly.lc d) with
    | none => ⟨AlgPoly.strip n, AlgPoly.strip d⟩
    | some inv => ⟨AlgPoly.scale inv n, AlgPoly.scale inv d⟩

def add (a b : AlgRatFn) : AlgRatFn :=
  simplify ⟨
    AlgPoly.add (AlgPoly.mul a.num b.den) (AlgPoly.mul b.num a.den),
    AlgPoly.mul a.den b.den
  ⟩

def mul (a b : AlgRatFn) : AlgRatFn :=
  simplify ⟨AlgPoly.mul a.num b.num, AlgPoly.mul a.den b.den⟩

def neg (a : AlgRatFn) : AlgRatFn := simplify ⟨AlgPoly.neg a.num, a.den⟩

def powNat (r : AlgRatFn) : Nat → AlgRatFn
  | 0 => ofPoly AlgPoly.one
  | n'+1 => mul (powNat r n') r

/-- Parse a K(v) expression (caller should `simplify` first). -/
partial def ofExpr? (e : Expr) (v : String) : Option AlgRatFn :=
  match AlgNum.ofExpr? e with
  | some α => some (ofConst α)
  | none =>
    match e with
    | .var name => if name == v then some (ofPoly AlgPoly.X) else none
    | .add a b =>
      match ofExpr? a v, ofExpr? b v with
      | some ra, some rb => some (add ra rb)
      | _, _ => none
    | .mul a b =>
      match ofExpr? a v, ofExpr? b v with
      | some ra, some rb => some (mul ra rb)
      | _, _ => none
    | .pow base (.const r) =>
      match CplxConst.toRat? r with
      | none => none
      | some q =>
        if q.den != 1 then none
        else
          match ofExpr? base v with
          | none => none
          | some rb =>
            if q.num ≥ 0 then some (powNat rb q.num.toNat)
            else
              if rb.num.isZero then none
              else some (simplify ⟨AlgPoly.powNat rb.den q.num.natAbs,
                                   AlgPoly.powNat rb.num q.num.natAbs⟩)
    | _ => none

def toExpr (r : AlgRatFn) (v : String) : Expr :=
  let r := simplify r
  if r.den.isOne then AlgPoly.toExpr r.num v
  else Expr.div (AlgPoly.toExpr r.num v) (AlgPoly.toExpr r.den v)

end AlgRatFn

end Taschenrechner
