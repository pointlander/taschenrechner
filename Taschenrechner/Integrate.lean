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

/-- Algebraic equivalence heuristic for verifying `F' = f`. -/
def exprsEquivalent (a b : Expr) (v : String := "x") : Bool :=
  let a0 := simplify a
  let b0 := simplify b
  if a0 == b0 then true
  else
    -- Trig normal form (tan→sin/cos, sin², product-to-sum, …)
    let aTrig := simplify (trigPreprocess a0)
    let bTrig := simplify (trigPreprocess b0)
    if aTrig == bTrig then true
    else
      let a1 := simplify (expand aTrig)
      let b1 := simplify (expand bTrig)
      if a1 == b1 || simplify (Expr.sub a1 b1) == zero then true
      else
        -- Compare as rational functions in `v` when possible
        match RatFn.ofExpr? a1 v, RatFn.ofExpr? b1 v with
        | some ra, some rb =>
          let ra := RatFn.simplify ra
          let rb := RatFn.simplify rb
          ra.num == rb.num && ra.den == rb.den
        | _, _ =>
          match RatFn.ofExpr? (Expr.sub a1 b1) v with
          | some r => (RatFn.simplify r).num.isZero
          | none =>
            -- One more trig pass on expanded forms
            simplify (trigPreprocess a1) == simplify (trigPreprocess b1)

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
    | sin _ | cos _ | tan _ => 2
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
      else .failure s!"cannot integrate power {e}"
    | _ =>
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
  Definite integral ∫_lo^hi e dv by evaluating the antiderivative
  (symbolic substitution only — no numeric eval of transcendentals).
-/
partial def subst (e : Expr) (v : String) (value : Expr) : Expr :=
  simplify (go e)
where
  go : Expr → Expr
    | const r => const r
    | var name => if name == v then value else var name
    | add a b => add (go a) (go b)
    | mul a b => mul (go a) (go b)
    | pow a b => pow (go a) (go b)
    | sin a => sin (go a)
    | cos a => cos (go a)
    | tan a => tan (go a)
    | exp a => exp (go a)
    | ln a => ln (go a)
    | atan a => atan (go a)
    | re a => re (go a)
    | im a => im (go a)
    | conj a => conj (go a)

def integrateDefinite (e : Expr) (v : String) (lo hi : Expr) : IntegrateResult :=
  match integrate e v with
  | .success F src =>
    -- Definite value inherits source; verification already done on F.
    .success (simplify (sub (subst F v hi) (subst F v lo))) src
  | .notElementary r => .notElementary r
  | .failure r => .failure r

/-- True iff `integrate` returns a verified elementary antiderivative. -/
def checkAntiderivative (e : Expr) (v : String := "x") : Bool :=
  match integrate e v with
  | .success F _ => verifyDerivative F e v
  | _ => false

end Taschenrechner.Expr
