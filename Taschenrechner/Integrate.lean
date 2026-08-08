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
import Taschenrechner.Risch

namespace Taschenrechner.Expr

/-- Result of attempted indefinite integration. -/
inductive IntegrateResult where
  | success (antideriv : Expr)
  | failure (reason : String)
  deriving Repr, Inhabited

namespace IntegrateResult

def map (f : Expr → Expr) : IntegrateResult → IntegrateResult
  | success e => success (f e)
  | failure r => failure r

def isSuccess : IntegrateResult → Bool
  | success _ => true
  | failure _ => false

def get? : IntegrateResult → Option Expr
  | success e => some e
  | failure _ => none

end IntegrateResult

/-- Recognise integer constant. -/
def asIntConst : Expr → Option Int
  | const r => if r.den == 1 then some r.num else none
  | _ => none

/-- Recognise rational constant. -/
def asRatConst : Expr → Option RatConst
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
          some (mul (const invN1) (pow (var v) (const n1)))
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
            | some inv => some (mul (const inv) (pow g (const n1)))
            | none => none
        | none =>
          if !dependsOn n v then
            some (div (pow g (add n one)) (add n one))
          else none
      else none
    | _ => none

/-- Detect `c * f` with rational `c`. -/
def peelConstFactor (e : Expr) : RatConst × Expr :=
  match e with
  | mul (const c) f => (c, f)
  | mul f (const c) => (c, f)
  | const c => (c, one)
  | e => (RatConst.one, e)

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
      | .failure _ => none
      | .success V =>
        let V := simplify V
        let integrand2 := simplify (mul V du)
        match integrateRec integrand2 v fuel' with
        | .failure _ => none
        | .success int2 =>
          some (simplify (sub (mul u V) int2))
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

/-- Core recursive integrator with fuel. -/
partial def integrateRaw (e : Expr) (v : String) (fuel : Nat) : IntegrateResult :=
  match fuel with
  | 0 => .failure "out of fuel"
  | fuel'+1 =>
    let e := simplify e
    -- Constant (no dependence on v)
    if !dependsOn e v then
      .success (mul e (var v))
    else
      -- Linearity over addition
      match e with
      | add a b =>
        match integrateRaw a v fuel', integrateRaw b v fuel' with
        | .success A, .success B => .success (simplify (add A B))
        | .failure r, _ => .failure r
        | _, .failure r => .failure r
      | _ =>
        -- Peel constant factor
        let (c, f) := peelConstFactor e
        if !c.isOne && f != e then
          match integrateRaw f v fuel' with
          | .success F => .success (simplify (mul (const c) F))
          | .failure r => .failure r
        else
          -- Table for pure elementary of the variable
          match tableIntegral e v with
          | some F => .success (simplify F)
          | none =>
            -- Power of the variable: x^n
            match e with
            | pow base expn =>
              match integratePower base expn v with
              | some F => .success (simplify F)
              | none => tryAdvanced e v fuel'
            | _ => tryAdvanced e v fuel'
where
  tryAdvanced (e : Expr) (v : String) (fuel' : Nat) : IntegrateResult :=
    -- 1/x form: x^(-1) may appear as pow, or as div
    match e with
    | pow (var name) (const r) =>
      if name == v && r == RatConst.negOne then
        .success (ln (var v))
      else .failure s!"cannot integrate power {e}"
    | _ =>
      -- Reverse chain rule
      match tryChainRule e v fuel' with
      | some F => .success (simplify F)
      | none =>
        -- Common composite forms: sin(ax+b), exp(ax), etc.
        match tryLinearComposite e v with
        | some F => .success (simplify F)
        | none =>
          -- Integration by parts
          match tryByParts e v fuel' integrateRaw with
          | some F => .success (simplify F)
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
          | some invA => some (mul (const invA) (antiAt inner))
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
      if name == v then some (a, RatConst.zero) else none
    | mul (var name) (const a) =>
      if name == v then some (a, RatConst.zero) else none
    | add a b =>
      match linearForm a v, asRatConst b with
      | some (ca, cb), some rb => some (ca, cb + rb)
      | _, _ =>
        match asRatConst a, linearForm b v with
        | some ra, some (ca, cb) => some (ca, cb + ra)
        | _, _ => none
    | const _ => none
    | _ => none

/-- Indefinite integral ∫ e dv. Returns simplified antiderivative or failure.

  Order:
  1. **Risch** (rational + transcendental exp/log decisions, including non-existence)
  2. Heuristic table / chain rule / by-parts (trig and remaining patterns)
-/
def integrate (e : Expr) (v : String := "x") : IntegrateResult :=
  let e := simplify e
  match risch e v with
  | .elementary F => .success (simplify F)
  | .notElementary reason =>
    .failure s!"not elementary (Risch): {reason}"
  | .undecided _ =>
    -- Fall back to heuristic integrator (sin/cos, by-parts, …)
    integrateRaw e v 64

/-- Convenience: optional antiderivative. -/
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

def integrateDefinite (e : Expr) (v : String) (lo hi : Expr) : IntegrateResult :=
  match integrate e v with
  | .failure r => .failure r
  | .success F =>
    .success (simplify (sub (subst F v hi) (subst F v lo)))

/-- Verify antiderivative by differentiation: d/dv (∫ e) ≈ e. -/
def checkAntiderivative (e : Expr) (v : String := "x") : Bool :=
  match integrate e v with
  | .failure _ => false
  | .success F =>
    let dF := diff F v
    simplify (expand dF) == simplify (expand e)
      || simplify dF == simplify e

end Taschenrechner.Expr
