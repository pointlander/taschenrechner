/-
  Symbolic indefinite integration (antiderivatives).

  Strategy (in order):
  1. Linearity and constant factors
  2. Table of elementary integrals
  3. Polynomial / power rule
  4. Reverse chain rule (∫ f'(g(x)) g'(x) dx)
  5. Simple substitution heuristics
  6. Basic integration by parts for u·v' patterns
-/
import Taschenrechner.Diff
import Taschenrechner.Simplify
import Taschenrechner.Trig
import Taschenrechner.Normal
import Taschenrechner.Eval
import Taschenrechner.Risch

namespace Taschenrechner.Expr

/-- Which integrator produced an antiderivative. -/
inductive IntegrateSource where
  | risch
  | heuristic
  deriving Repr, BEq, DecidableEq, Inhabited

namespace IntegrateSource

def toString : IntegrateSource → String
  | risch => "risch"
  | heuristic => "heuristic"

instance : ToString IntegrateSource where
  toString := toString

end IntegrateSource

/--
  Structured result of indefinite integration.

  * `success` — elementary antiderivative; `source` records the engine;
    only returned when automatic derivative verification passes (`F' = f`).
  * `notElementary` — Risch (or another decision procedure) proved no
    elementary antiderivative exists.
  * `failure` — could not integrate, or a candidate `F` failed verification.
-/
inductive IntegrateResult where
  | success (antideriv : Expr) (source : IntegrateSource)
  | notElementary (reason : String)
  | failure (reason : String)
  deriving Repr, Inhabited

namespace IntegrateResult

def map (f : Expr → Expr) : IntegrateResult → IntegrateResult
  | success e src => success (f e) src
  | notElementary r => notElementary r
  | failure r => failure r

def isSuccess : IntegrateResult → Bool
  | success _ _ => true
  | _ => false

def isNotElementary : IntegrateResult → Bool
  | notElementary _ => true
  | _ => false

def get? : IntegrateResult → Option Expr
  | success e _ => some e
  | _ => none

def getSource? : IntegrateResult → Option IntegrateSource
  | success _ s => some s
  | _ => none

def reason? : IntegrateResult → Option String
  | notElementary r => some r
  | failure r => some r
  | success _ _ => none

def toString : IntegrateResult → String
  | success F src => s!"success ({src}): {F}"
  | notElementary r => s!"not elementary: {r}"
  | failure r => s!"failure: {r}"

instance : ToString IntegrateResult where
  toString := toString

end IntegrateResult

/--
  Factors that clear inverse powers: for each `base^q` with `q < 0`,
  include `base^{-q}` (so `u^{-1/2}` contributes `u^{1/2}`, `u^{-1}` contributes `u`).
-/
partial def invClearFactors : Expr → List Expr
  | mul a b => invClearFactors a ++ invClearFactors b
  | pow base (const r) =>
    match CplxConst.toRat? r with
    | some q =>
      if q.num < 0 then
        let pos := RatConst.neg q
        pow base (ofRat pos) :: invClearFactors base
      else invClearFactors base
    | none => invClearFactors base
  | pow base e => invClearFactors base ++ invClearFactors e
  | add a b => invClearFactors a ++ invClearFactors b
  | sin e | cos e | tan e | sinh e | cosh e | tanh e
  | exp e | ln e | atan e | abs e | re e | im e | conj e => invClearFactors e
  | eq a b | lt a b | le a b => invClearFactors a ++ invClearFactors b
  | _ => []

/-- Multiply by clear-factors from `a` and `b` so expand can cancel radicals. -/
def clearInvFactors (e : Expr) (extras : List Expr) : Expr :=
  let fs := (invClearFactors e ++ extras).eraseDups
  fs.foldl (fun acc f => mul acc f) e

/-- Algebraic equivalence heuristic for verifying `F' = f`. -/
def exprsEquivalent (a b : Expr) (v : String := "x") : Bool :=
  -- Prefer full normal forms + trig preprocess
  let a0 := simplify (trigPreprocess a)
  let b0 := simplify (trigPreprocess b)
  if a0 == b0 then true
  else if equivNF a0 b0 v then true
  else
    let a1 := simplify (expand a0)
    let b1 := simplify (expand b0)
    if equivNF a1 b1 v || isZeroExpr (sub a1 b1) v then true
    else
      -- Clear inverse powers (√ and other denominators), expand, repeat.
      -- Proves identities such as d/dx ln(x+√(x²+1)) = 1/√(x²+1)
      -- and d/dx (x/2 √(x²+1) + 1/2 ln(...)) = √(x²+1).
      let rec clearLoop (n : Nat) (a b : Expr) : Bool :=
        match n with
        | 0 => false
        | n'+1 =>
          let extras := invClearFactors a ++ invClearFactors b
          -- Always try expand-only step; also clear inverses when present
          let aw0 := simplify (expand a)
          let bw0 := simplify (expand b)
          if aw0 == bw0 || equivNF aw0 bw0 v || isZeroExpr (sub aw0 bw0) v then true
          else if extras.isEmpty then
            if aw0 == a && bw0 == b then false
            else clearLoop n' aw0 bw0
          else
            let aw := simplify (expand (clearInvFactors a extras))
            let bw := simplify (expand (clearInvFactors b extras))
            -- Also prove a − b = 0 after clearing (and with constant weight 2)
            let dw := simplify (expand (clearInvFactors (sub a b) extras))
            let dw2 := simplify (expand (mul (ofInt 2) dw))
            if aw == bw || equivNF aw bw v || isZeroExpr (sub aw bw) v
                || isZeroExpr dw v || isZeroExpr dw2 v then true
            else if aw == a && bw == b then false
            else clearLoop n' aw bw
      clearLoop 12 a0 b0

/-- Check that `diff F v` matches integrand `f`. -/
def verifyDerivative (F f : Expr) (v : String := "x") : Bool :=
  exprsEquivalent (diff F v) f v

/--
  Accept candidate `F` only if `F' = f`.
  On mismatch, return a structured verification failure (not a silent wrong answer).
-/
def acceptAntideriv (F f : Expr) (v : String) (source : IntegrateSource) : IntegrateResult :=
  let F := simplify F
  let f := simplify f
  let F' := diff F v
  if exprsEquivalent F' f v then
    .success F source
  else
    .failure s!"verification failed ({source}): d/d{v}({F}) = {simplify F'}, expected {f}"

/-- Recognise integer constant (real). -/
def asIntConst : Expr → Option Int
  | const r =>
    match CplxConst.toRat? r with
    | some q => if q.den == 1 then some q.num else none
    | none => none
  | _ => none

/-- Recognise real rational constant. -/
def asRatConst : Expr → Option RatConst
  | const r => CplxConst.toRat? r
  | _ => none

/-- Recognise any complex constant. -/
def asCplxConst : Expr → Option CplxConst
  | const r => some r
  | _ => none

/-- Table lookup for elementary antiderivatives of `f(v)` where arg is the variable. -/
def tableIntegral (e : Expr) (v : String) : Option Expr :=
  match e with
  | var name =>
    if name == v then some (div (pow (var v) (ofInt 2)) (ofInt 2))  -- ∫ x dx = x²/2
    else some (mul e (var v))  -- ∫ c dx = c·x for free c? handled elsewhere
  | sin (var name) =>
    if name == v then some (neg (cos (var v))) else none
  | cos (var name) =>
    if name == v then some (sin (var v)) else none
  | tan (var name) =>
    -- ∫ tan x = -ln|cos x|
    if name == v then some (neg (ln (cos (var v)))) else none
  | exp (var name) =>
    if name == v then some (exp (var v)) else none
  | ln (var name) =>
    -- ∫ ln x = x ln x - x
    if name == v then
      some (sub (mul (var v) (ln (var v))) (var v))
    else none
  | _ => none

/-! ### Radical (square-root quadratic) integral table -/

/-- Half as a complex constant. -/
private def halfC : CplxConst := CplxConst.ofRat ⟨1, 2⟩

/-- Is this `1/2` as a power exponent? -/
private def isHalf : Expr → Bool
  | const r =>
    match CplxConst.toRat? r with
    | some q => q == ⟨1, 2⟩
    | none => false
  | _ => false

/-- Is this `-1/2` as a power exponent? -/
private def isNegHalf : Expr → Bool
  | const r =>
    match CplxConst.toRat? r with
    | some q => q == ⟨-1, 2⟩
    | none => false
  | _ => false

/--
  Match `x² + a²`, `x² - a²`, or `a² - x²` with rational `a² ≥ 0` (as expression).
  Returns `(a²_expr, kind)` where kind: 0 = x²+a², 1 = x²−a², 2 = a²−x².
-/
def matchQuadUnderSqrt (e : Expr) (v : String) : Option (Expr × Nat) :=
  let e := simplify e
  match e with
  | add a b =>
    match a, b with
    | pow (var name) (const r), const c =>
      if name == v && r == CplxConst.ofInt 2 then
        match CplxConst.toRat? c with
        | some q =>
          if q.num ≥ 0 then some (const c, 0)  -- x² + a²
          else
            -- x² + (−a²) = x² − a²
            some (const (CplxConst.neg c), 1)
        | none => none
      else none
    | const c, pow (var name) (const r) =>
      if name == v && r == CplxConst.ofInt 2 then
        match CplxConst.toRat? c with
        | some q =>
          if q.num ≥ 0 then some (const c, 0)
          else some (const (CplxConst.neg c), 1)
        | none => none
      else none
    | pow (var name) (const r), mul (const c) rest =>
      -- x² + (−1)·a² after simplify of x² − a²
      if name == v && r == CplxConst.ofInt 2 && c.isNegOne then
        match rest with
        | const a2 =>
          match CplxConst.toRat? a2 with
          | some q => if q.num > 0 then some (const a2, 1) else none
          | none => none
        | _ => none
      else none
    | mul (const c) rest, pow (var name) (const r) =>
      -- (−1)·x² + a² = a² − x²
      if name == v && r == CplxConst.ofInt 2 && c.isNegOne then
        match rest with
        | var name' =>
          if name' == v then
            -- only -x², need a² from elsewhere — not this form alone
            none
          else none
        | _ => none
      else none
    | const c, mul (const k) (pow (var name) (const r)) =>
      -- a² + (−1)·x²
      if name == v && r == CplxConst.ofInt 2 && k.isNegOne then
        match CplxConst.toRat? c with
        | some q => if q.num > 0 then some (const c, 2) else none
        | none => none
      else none
    | mul (const k) (pow (var name) (const r)), const c =>
      -- (−1)·x² + a²
      if name == v && r == CplxConst.ofInt 2 && k.isNegOne then
        match CplxConst.toRat? c with
        | some q => if q.num > 0 then some (const c, 2) else none
        | none => none
      else none
    | _, _ => none
  | _ => none

/-- √e as expression. -/
private def sqrtE (e : Expr) : Expr := Taschenrechner.sqrt e

/-- Antiderivative for √(quad) forms. -/
def radicalSqrtIntegral (base : Expr) (a2 : Expr) (kind : Nat) (v : String) : Option Expr :=
  let x := var v
  let s := sqrtE base
  match kind with
  | 0 =>
    -- ∫ √(x²+a²) = x/2 √(x²+a²) + a²/2 ln(x + √(x²+a²))
    some (simplify (add
      (mul (const halfC) (mul x s))
      (mul (const halfC) (mul a2 (ln (add x s))))))
  | 1 =>
    -- ∫ √(x²−a²) = x/2 √(x²−a²) − a²/2 ln|x + √(x²−a²)|
    some (simplify (sub
      (mul (const halfC) (mul x s))
      (mul (const halfC) (mul a2 (ln (add x s))))))
  | 2 =>
    -- ∫ √(a²−x²) = x/2 √(a²−x²) + a²/2 atan(x/√(a²−x²))
    some (simplify (add
      (mul (const halfC) (mul x s))
      (mul (const halfC) (mul a2 (atan (div x s))))))
  | _ => none

/-- Antiderivative for 1/√(quad) forms. -/
def radicalInvSqrtIntegral (base : Expr) (a2 : Expr) (kind : Nat) (v : String) : Option Expr :=
  let x := var v
  let s := sqrtE base
  let _ := a2
  match kind with
  | 0 | 1 =>
    -- ∫ 1/√(x²±a²) = ln|x + √(x²±a²)|
    some (simplify (ln (add x s)))
  | 2 =>
    -- ∫ 1/√(a²−x²) = atan(x/√(a²−x²))  (= arcsin(x/a))
    some (simplify (atan (div x s)))
  | _ => none

/--
  Table for ∫ R(x, √(±x²±a²)) of the common textbook forms:
  * 1/√(x²+a²), 1/√(x²−a²), 1/√(a²−x²)
  * √(x²+a²), √(x²−a²), √(a²−x²)
-/
partial def radicalIntegral (e : Expr) (v : String) : Option Expr :=
  let e := simplify e
  match e with
  | pow base expn =>
    if isNegHalf expn then
      -- 1/√(±x²±a²) — verified via clear-inverse + expand
      match matchQuadUnderSqrt base v with
      | some (a2, kind) => radicalInvSqrtIntegral base a2 kind v
      | none => none
    else if isHalf expn then
      -- √(±x²±a²); only if F' checks with the same exprsEquivalent as acceptAntideriv
      match matchQuadUnderSqrt base v with
      | some (a2, kind) =>
        match radicalSqrtIntegral base a2 kind v with
        | some F =>
          if exprsEquivalent (diff F v) e v then some F else none
        | none => none
      | none => none
    else none
  | mul (const c) rest =>
    -- c / √(quad) or c · √(quad)
    if c.isZero then some zero
    else
      match radicalIntegral rest v with
      | some F => some (simplify (mul (const c) F))
      | none => none
  | mul rest (const c) =>
    radicalIntegral (mul (const c) rest) v
  | _ => none

/-- Power rule: ∫ u^n · u'  and ∫ x^n dx. -/
def integratePower (base expn : Expr) (v : String) : Option Expr :=
  -- ∫ x^n dx
  if base == var v then
    match asRatConst expn with
    | some r =>
      -- special case n = -1 → ln|x|
      if r == RatConst.negOne then
        some (ln (var v))
      else
        -- x^(n+1)/(n+1)
        let n1 := r + RatConst.one
        match RatConst.inv n1 with
        | some invN1 =>
          some (mul (ofRat invN1) (pow (var v) (ofRat n1)))
        | none => none
    | none =>
      -- symbolic exponent independent of v: x^a → x^(a+1)/(a+1)
      if !dependsOn expn v then
        some (div (pow (var v) (add expn one)) (add expn one))
      else none
  else none

/--
  Try reverse chain rule:
  if integrand = f(g(x)) * g'(x), return F(g(x)) where F' = f.
-/
partial def tryChainRule (e : Expr) (v : String) (_fuel : Nat) : Option Expr :=
  -- Pattern: f(g) * g'  as a product
  let factors := flattenMul e
  if factors.length < 2 then none
  else
    -- Common reverse-chain patterns:
    --   cos(g) * g'  → sin(g)
    --   sin(g) * g'  → -cos(g)
    --   exp(g) * g'  → exp(g)
    --   g^n * g'     → g^(n+1)/(n+1)
    tryPairs factors
where
  tryPairs (fs : List Expr) : Option Expr :=
    let n := fs.length
    let rec go (i : Nat) : Option Expr :=
      if i ≥ n then none
      else
        match fs[i]? with
        | none => none
        | some fi =>
          match tryAsDerivProduct fi (fs.eraseIdx i) with
          | some r => some r
          | none => go (i+1)
    go 0

  tryAsDerivProduct (candidate : Expr) (rest : List Expr) : Option Expr :=
    let restProd := foldMul rest
    match candidate with
    | cos g =>
      if simplify (diff g v) == simplify restProd then some (sin g)
      else if simplify (neg (diff g v)) == simplify restProd then some (neg (sin g))
      else none
    | sin g =>
      if simplify (diff g v) == simplify restProd then some (neg (cos g))
      else if simplify (neg (diff g v)) == simplify restProd then some (cos g)
      else none
    | exp g =>
      if simplify (diff g v) == simplify restProd then some (exp g)
      else none
    | pow g n =>
      -- g^n * g' → g^(n+1)/(n+1)
      let g' := simplify (diff g v)
      if g' == simplify restProd then
        match asRatConst n with
        | some r =>
          if r == RatConst.negOne then some (ln g)
          else
            let n1 := r + RatConst.one
            match RatConst.inv n1 with
            | some inv => some (mul (ofRat inv) (pow g (ofRat n1)))
            | none => none
        | none =>
          if !dependsOn n v then
            some (div (pow g (add n one)) (add n one))
          else none
      else none
    | _ => none

/-- Detect `c * f` with rational `c`. -/
def peelConstFactor (e : Expr) : CplxConst × Expr :=
  match e with
  | mul (const c) f => (c, f)
  | mul f (const c) => (c, f)
  | const c => (c, one)
  | e => (CplxConst.one, e)

/-- Integration by parts: ∫ u dv = u v − ∫ v du, for simple polynomial × elementary. -/
partial def tryByParts (e : Expr) (v : String) (fuel : Nat)
    (integrateRec : Expr → String → Nat → IntegrateResult) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let factors := flattenMul e
    -- Prefer u = polynomial/var/ln, dv = the rest
    chooseU factors |>.bind fun (u, rest) =>
      let du := simplify (diff u v)
      let dv := foldMul rest
      -- V = ∫ dv  (must succeed without by-parts again if possible)
      match integrateRec dv v fuel' with
      | .success V _ =>
        let V := simplify V
        let integrand2 := simplify (mul V du)
        match integrateRec integrand2 v fuel' with
        | .success int2 _ =>
          some (simplify (sub (mul u V) int2))
        | _ => none
      | _ => none
where
  /-- LIATE-ish priority: ln > algebraic (var/pow) > trig > exp. -/
  priority : Expr → Nat
    | ln _ => 0
    | var _ => 1
    | pow (var _) _ => 1
    | sin _ | cos _ | tan _ | sinh _ | cosh _ | tanh _ => 2
    | exp _ => 3
    | _ => 4
  chooseU (fs : List Expr) : Option (Expr × List Expr) :=
    if fs.length < 2 then none
    else
      let ranked := fs.mapIdx fun i f => (priority f, i, f)
      let ranked := ranked.toArray.qsort (fun a b => a.1 < b.1) |>.toList
      match ranked with
      | (_, i, u) :: _ =>
        if priority u ≥ 3 then none  -- don't pick exp as u usually
        else some (u, fs.eraseIdx i)
      | [] => none

/-- Heuristic integrator (no derivative check; caller verifies). -/
partial def integrateRaw (e : Expr) (v : String) (fuel : Nat) : IntegrateResult :=
  match fuel with
  | 0 => .failure "out of fuel"
  | fuel'+1 =>
    let e := simplify e
    -- Constant (no dependence on v)
    if !dependsOn e v then
      .success (mul e (var v)) .heuristic
    else
      -- Linearity over addition
      match e with
      | add a b =>
        match integrateRaw a v fuel', integrateRaw b v fuel' with
        | .success A _, .success B _ => .success (simplify (add A B)) .heuristic
        | .notElementary r, _ => .notElementary r
        | _, .notElementary r => .notElementary r
        | .failure r, _ => .failure r
        | _, .failure r => .failure r
      | _ =>
        -- Peel constant factor
        let (c, f) := peelConstFactor e
        if !(c.isOne) && f != e then
          match integrateRaw f v fuel' with
          | .success F _ => .success (simplify (mul (const c) F)) .heuristic
          | .notElementary r => .notElementary r
          | .failure r => .failure r
        else
          -- Table for pure elementary of the variable
          match tableIntegral e v with
          | some F => .success (simplify F) .heuristic
          | none =>
            -- Power of the variable: x^n
            match e with
            | pow base expn =>
              match integratePower base expn v with
              | some F => .success (simplify F) .heuristic
              | none => tryAdvanced e v fuel'
            | _ => tryAdvanced e v fuel'
where
  tryAdvanced (e : Expr) (v : String) (fuel' : Nat) : IntegrateResult :=
    -- 1/x form: x^(-1) may appear as pow, or as div
    match e with
    | pow (var name) (const r) =>
      if name == v && r == CplxConst.negOne then
        .success (ln (var v)) .heuristic
      else
        -- radical powers √(quad), 1/√(quad)
        match radicalIntegral e v with
        | some F => .success (simplify F) .heuristic
        | none => .failure s!"cannot integrate power {e}"
    | _ =>
      -- Radical table (also non-power spellings after simplify)
      match radicalIntegral e v with
      | some F => .success (simplify F) .heuristic
      | none =>
        -- Reverse chain rule
        match tryChainRule e v fuel' with
        | some F => .success (simplify F) .heuristic
        | none =>
          -- Common composite forms: sin(ax+b), exp(ax), etc.
          match tryLinearComposite e v with
          | some F => .success (simplify F) .heuristic
          | none =>
            -- Integration by parts
            match tryByParts e v fuel' integrateRaw with
            | some F => .success (simplify F) .heuristic
            | none => .failure s!"cannot integrate: {e}"

  /-- ∫ f(ax+b) dx for elementary f. -/
  tryLinearComposite (e : Expr) (v : String) : Option Expr :=
    let tryLin (inner : Expr) (antiAt : Expr → Expr) : Option Expr :=
      -- inner = a*v + b ?
      match linearForm inner v with
      | some (a, _b) =>
        if a.isZero then none
        else
          match RatConst.inv a with
          | some invA => some (mul (ofRat invA) (antiAt inner))
          | none => none
      | none =>
        if inner == var v then some (antiAt (var v))
        else none
    match e with
    | sin inner => tryLin inner fun u => neg (cos u)
    | cos inner => tryLin inner fun u => sin u
    | exp inner => tryLin inner fun u => exp u
    | tan inner => tryLin inner fun u => neg (ln (cos u))
    | pow (sin inner) (const r) =>
      -- ∫ sin², cos² not fully general; skip unless r=1
      if r.isOne then tryLin inner fun u => neg (cos u) else none
    | pow (cos inner) (const r) =>
      if r.isOne then tryLin inner fun u => sin u else none
    | _ => none

  /-- Match `a*v + b` with rationals a,b (b may be 0). -/
  linearForm (e : Expr) (v : String) : Option (RatConst × RatConst) :=
    let e := simplify e
    match e with
    | var name => if name == v then some (RatConst.one, RatConst.zero) else none
    | mul (const a) (var name) =>
      match CplxConst.toRat? a with
      | some q => if name == v then some (q, RatConst.zero) else none
      | none => none
    | mul (var name) (const a) =>
      match CplxConst.toRat? a with
      | some q => if name == v then some (q, RatConst.zero) else none
      | none => none
    | add a b =>
      match linearForm a v, asRatConst b with
      | some (ca, cb), some rb => some (ca, cb + rb)
      | _, _ =>
        match asRatConst a, linearForm b v with
        | some ra, some (ca, cb) => some (ca, cb + ra)
        | _, _ => none
    | const _ => none
    | _ => none

/-- Indefinite integral ∫ e dv with structured result and automatic verification.

  Order:
  1. **Risch** (rational + transcendental exp/log decisions, including non-existence)
  2. Heuristic table / chain rule / by-parts (trig and remaining patterns)

  Every successful antiderivative is checked: `diff F v ≈ e`. Mismatches become
  `.failure` with a verification message (never a silent wrong answer).
-/
def integrate (e : Expr) (v : String := "x") : IntegrateResult :=
  let e := simplify e
  match risch e v with
  | .elementary F => acceptAntideriv F e v .risch
  | .notElementary reason => .notElementary reason
  | .undecided _ =>
    match integrateRaw e v 64 with
    | .success F _ => acceptAntideriv F e v .heuristic
    | .notElementary r => .notElementary r
    | .failure r => .failure r

/-- Convenience: optional antiderivative (verified only). -/
def integrate? (e : Expr) (v : String := "x") : Option Expr :=
  (integrate e v).get?

/--
  Definite integral ∫_lo^hi e dv via the FTC:
  compute antiderivative F, then F(hi) − F(lo).
  Ground results are exact-evaluated over ℚ(i) when possible.
-/
def integrateDefinite (e : Expr) (v : String) (lo hi : Expr) : IntegrateResult :=
  match integrate e v with
  | .success F src =>
    let val := simplify (sub (subst F v hi) (subst F v lo))
    let val :=
      match Taschenrechner.eval? val with
      | some c => const c
      | none => val
    .success val src
  | .notElementary r => .notElementary r
  | .failure r => .failure r

/-- True iff `integrate` returns a verified elementary antiderivative. -/
def checkAntiderivative (e : Expr) (v : String := "x") : Bool :=
  match integrate e v with
  | .success F _ => verifyDerivative F e v
  | _ => false

end Taschenrechner.Expr
