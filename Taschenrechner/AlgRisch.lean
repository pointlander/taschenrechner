/-
  Algebraic Risch for a single quadratic (or linear) radical:
  ∫ R(x, √p(x)) dx with p ∈ K[x], deg p ≤ 2, K a real multiquadratic field.

  Strategy:
  1. Rewrite the integrand as A + B √p with A, B ∈ K(x)
  2. Linear p: t = √p
     Quadratic p: Euler substitution (√a·x + t, or x t + √c, or t(x−α))
  3. Integrate the resulting rational function in t over K(t)
  4. Substitute t back in terms of x and √p

  Nested towers and algebraic curves of genus ≥ 1 (deg p ≥ 3 square-free)
  are not decided here.
-/
import Taschenrechner.AlgNum
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.RatInt
import Taschenrechner.Normal

namespace Taschenrechner

open Expr

/-- Dummy substitution variable (substituted back before returning). -/
def eulerTName : String := "__t"

/-- Exponent is `1/2`. -/
def isHalfExp : Expr → Bool
  | const r =>
    match CplxConst.toRat? r with
    | some q => q == ⟨1, 2⟩
    | none => false
  | _ => false

/-- Exponent is `-1/2`. -/
def isNegHalfExp : Expr → Bool
  | const r =>
    match CplxConst.toRat? r with
    | some q => q == ⟨-1, 2⟩
    | none => false
  | _ => false

/-- Polynomial `n·d` for a K(v) rational `n/d` (so `√(n/d) = √(n d)/d`). -/
def radicandPoly? (base : Expr) (v : String) : Option AlgPoly :=
  match AlgRatFn.ofExpr? (simplify base) v with
  | none => none
  | some r =>
    let r := AlgRatFn.canceled r
    if r.den.isZero || r.num.isZero then none
    else some (AlgPoly.mul r.num r.den)

/-- Odd-multiplicity square-free kernel of `p` (monic). -/
def oddKernel (p : AlgPoly) : AlgPoly :=
  let (_c, facs) := AlgPoly.squareFreeFactor p
  let k :=
    facs.foldl (fun acc (s, m) =>
      if m % 2 == 1 then AlgPoly.mul acc s else acc) AlgPoly.one
  let k := AlgPoly.monic (AlgPoly.strip k)
  if k.isZero || k.deg ≤ 0 then AlgPoly.one else k

/-- Square part `∏ s_i^{⌊m_i/2⌋}` from Yun factorization of `p`. -/
def evenSqrtPoly (p : AlgPoly) : AlgPoly × AlgNum :=
  let (c, facs) := AlgPoly.squareFreeFactor p
  let sq :=
    facs.foldl (fun acc (s, m) =>
      AlgPoly.mul acc (AlgPoly.powNat s (m / 2))) AlgPoly.one
  (AlgPoly.strip sq, c)

/-- Same monic kernel? -/
def sameKernel (a b : AlgPoly) : Bool :=
  let a := AlgPoly.monic (AlgPoly.strip a)
  let b := AlgPoly.monic (AlgPoly.strip b)
  a.deg == b.deg && a.deg ≥ 1 && a == b

/-- Insert a deg ≥ 1 kernel uniquely. -/
def insertKernel (p : AlgPoly) (ks : List AlgPoly) : List AlgPoly :=
  let p := AlgPoly.monic (AlgPoly.strip p)
  if p.isOne || p.deg ≤ 0 then ks
  else if ks.any (sameKernel p) then ks
  else ks ++ [p]

/-- Merge kernel lists, uniqued. -/
def mergeKernels (as bs : List AlgPoly) : List AlgPoly :=
  (as ++ bs).foldl (fun acc p => insertKernel p acc) []

/-- Kernels of all `√q` with `q ∈ K(v)` appearing in `e`. -/
partial def collectKernels (e : Expr) (v : String) : List AlgPoly :=
  match e with
  | pow base expn =>
    let rest := mergeKernels (collectKernels base v) (collectKernels expn v)
    if isHalfExp expn || isNegHalfExp expn then
      match radicandPoly? base v with
      | some q => insertKernel (oddKernel q) rest
      | none => rest
    else
      match expn with
      | const r =>
        match CplxConst.toRat? r with
        | some q =>
          if q.den == 2 then
            match radicandPoly? base v with
            | some poly => insertKernel (oddKernel poly) rest
            | none => rest
          else rest
        | none => rest
      | _ => rest
  | add a b | mul a b => mergeKernels (collectKernels a v) (collectKernels b v)
  | sin a | cos a | tan a | sinh a | cosh a | tanh a
  | exp a | ln a | atan a | asin a | acos a | sec a | csc a | cot a
  | factorial a | gamma a | floor a | abs a | re a | im a | conj a =>
      collectKernels a v
  | Expr.ite c t els =>
      mergeKernels (collectKernels c v)
        (mergeKernels (collectKernels t v) (collectKernels els v))
  | eq a b | lt a b | le a b => mergeKernels (collectKernels a v) (collectKernels b v)
  | const _ | var _ | mat _ => []

/-- Unique deg-1 or deg-2 kernel, if any. -/
def uniqueQuadKernel? (e : Expr) (v : String) : Option AlgPoly :=
  match collectKernels (simplify e) v with
  | [p] =>
    if p.deg == 1 || p.deg == 2 then some p else none
  | _ => none

/-! ### Field K(x)(√p) as pairs `A + B √p` -/

structure AlgSqrtFn where
  p : AlgPoly
  a : AlgRatFn
  b : AlgRatFn
  deriving Repr, Inhabited

namespace AlgSqrtFn

def ofRatFn (p : AlgPoly) (r : AlgRatFn) : AlgSqrtFn := ⟨p, r, AlgRatFn.zero⟩
def ofSqrt (p : AlgPoly) : AlgSqrtFn := ⟨p, AlgRatFn.zero, AlgRatFn.ofPoly AlgPoly.one⟩

def add (u w : AlgSqrtFn) : AlgSqrtFn :=
  ⟨u.p, AlgRatFn.add u.a w.a, AlgRatFn.add u.b w.b⟩

def neg (u : AlgSqrtFn) : AlgSqrtFn :=
  ⟨u.p, AlgRatFn.neg u.a, AlgRatFn.neg u.b⟩

def mul (u w : AlgSqrtFn) : AlgSqrtFn :=
  let pFn := AlgRatFn.ofPoly u.p
  let aa := AlgRatFn.mul u.a w.a
  let bb := AlgRatFn.mul pFn (AlgRatFn.mul u.b w.b)
  let ab := AlgRatFn.mul u.a w.b
  let ba := AlgRatFn.mul u.b w.a
  ⟨u.p, AlgRatFn.add aa bb, AlgRatFn.add ab ba⟩

def inv? (u : AlgSqrtFn) : Option AlgSqrtFn :=
  let pFn := AlgRatFn.ofPoly u.p
  let d :=
    AlgRatFn.add (AlgRatFn.mul u.a u.a)
      (AlgRatFn.neg (AlgRatFn.mul pFn (AlgRatFn.mul u.b u.b)))
  match AlgRatFn.inv d with
  | none => none
  | some dinv =>
    some ⟨u.p, AlgRatFn.mul u.a dinv, AlgRatFn.mul (AlgRatFn.neg u.b) dinv⟩

def powNat (u : AlgSqrtFn) : Nat → AlgSqrtFn
  | 0 => ofRatFn u.p (AlgRatFn.ofPoly AlgPoly.one)
  | n'+1 => mul (powNat u n') u

/-- `√base` in K(x)(√p), when the odd kernel of `base` is `p` (or a square). -/
def ofSqrtBase? (base : Expr) (v : String) (p : AlgPoly) : Option AlgSqrtFn :=
  match AlgRatFn.ofExpr? (simplify base) v with
  | none => none
  | some r0 =>
    let r0 := AlgRatFn.canceled r0
    if r0.den.isZero then none
    else
      let q := AlgPoly.mul r0.num r0.den
      let ker := oddKernel q
      let (sq, c) := evenSqrtPoly q
      let sqrtC : Option AlgNum :=
        match AlgNum.sqrt? c with
        | some s => some s
        | none => AlgNum.ofExpr? (sqrt (AlgNum.toExpr c))
      match sqrtC with
      | none => none
      | some sc =>
        -- √(n/d) = √(n d)/d = (√c · sq · √ker) / d
        match AlgRatFn.div (AlgRatFn.mul (AlgRatFn.ofConst sc) (AlgRatFn.ofPoly sq))
              (AlgRatFn.ofPoly r0.den) with
        | none => none
        | some scale =>
          if ker.isOne || ker.deg ≤ 0 then
            some (ofRatFn p scale)
          else if sameKernel ker p then
            some ⟨p, AlgRatFn.zero, scale⟩
          else none

/-- Parse `e` as an element of K(v)(√p). -/
partial def ofExpr? (e : Expr) (v : String) (p : AlgPoly) : Option AlgSqrtFn :=
  let e := simplify e
  match AlgRatFn.ofExpr? e v with
  | some r => some (ofRatFn p r)
  | none =>
    match e with
    | Expr.add u w =>
      match ofExpr? u v p, ofExpr? w v p with
      | some a, some b => some (add a b)
      | _, _ => none
    | Expr.mul u w =>
      match ofExpr? u v p, ofExpr? w v p with
      | some a, some b => some (mul a b)
      | _, _ => none
    | Expr.pow base expn =>
      match expn with
      | Expr.const r =>
        match CplxConst.toRat? r with
        | none => none
        | some q =>
          if isHalfExp expn then ofSqrtBase? base v p
          else if isNegHalfExp expn then
            match ofSqrtBase? base v p with
            | some s => inv? s
            | none => none
          else if q.den == 2 then
            -- u^{n/2} = (√u)^n
            match ofSqrtBase? base v p with
            | none => none
            | some s =>
              let sN := powNat s q.num.natAbs
              if q.num ≥ 0 then some sN else inv? sN
          else if q.den == 1 then
            match ofExpr? base v p with
            | none => none
            | some s =>
              if q.num ≥ 0 then some (powNat s q.num.toNat)
              else
                match inv? s with
                | some s' => some (powNat s' q.num.natAbs)
                | none => none
          else none
      | _ => none
    | _ => none

def toExpr (u : AlgSqrtFn) (v : String) : Expr :=
  let pE := sqrt (AlgPoly.toExpr u.p v)
  let aE := AlgRatFn.toExpr u.a v
  let bE := AlgRatFn.toExpr u.b v
  simplify (Expr.add aE (Expr.mul bE pE))

end AlgSqrtFn

/-! ### Euler substitutions -/

/-- Run `x(t), y(t) = √p` substitution: integrand `(A(x)+B(x) y) x'` in `t`. -/
def runEulerSubst (A B : AlgRatFn) (v tName : String)
    (xOfT yOfT tBack : Expr) : Option Expr :=
  let xOfT := simplify xOfT
  let yOfT := simplify yOfT
  if dependsOn xOfT v || dependsOn yOfT v then none
  else
    match AlgRatFn.ofExpr? xOfT tName, AlgRatFn.ofExpr? yOfT tName with
    | some xFn, some yFn =>
      let dx := AlgRatFn.differentiate xFn
      -- Degree cap: substitution should stay a modest rational in t.
      if xFn.den.deg > 8 || dx.den.deg > 12 then none
      else
        let AE := subst (AlgRatFn.toExpr A v) v xOfT
        let BE := subst (AlgRatFn.toExpr B v) v xOfT
        match AlgRatFn.ofExpr? (simplify AE) tName,
              AlgRatFn.ofExpr? (simplify BE) tName with
        | some Af, some Bf =>
          let integrand :=
            AlgRatFn.mul (AlgRatFn.add Af (AlgRatFn.mul Bf yFn)) dx
          if integrand.den.deg > 16 || integrand.num.deg > 16 then none
          else
            match integrateRationalAlgPoly integrand.num integrand.den tName with
            | none => none
            | some Ft =>
              let Fx := simplify (subst Ft tName (simplify tBack))
              if dependsOn Fx tName then none else some Fx
        | _, _ => none
    | _, _ => none

/-- Linear coefficient of `A` in `v` (0 if not a polynomial). -/
def linScore (A : AlgRatFn) : Int :=
  if !A.den.isOne then 0
  else
    match AlgNum.toRat? (AlgPoly.coeff A.num 1) with
    | some q => q.num
    | none => 0

/--
  Canonicalize `ln(A + B √p)` so the rational part has a nonnegative `x`
  coefficient: `ln(√p − x) = −ln(√p + x)` (up to a constant).
-/
partial def canonLnWalk (e : Expr) (p : AlgPoly) (v : String) : Expr :=
  match e with
  | ln u =>
    let u := simplify u
    match AlgSqrtFn.ofExpr? u v p with
    | none => ln (canonLnWalk u p v)
    | some s =>
      if s.b.num.isZero then ln (AlgRatFn.toExpr s.a v)
      else if linScore s.a ≥ 0 then
        ln (AlgSqrtFn.toExpr s v)
      else
        -- (A+B√p)(−A+B√p) = B²p − A² = −N
        -- ln(s) = ln(−N) − ln(−A + B√p)
        let pFn := AlgRatFn.ofPoly p
        let N :=
          AlgRatFn.add (AlgRatFn.mul s.a s.a)
            (AlgRatFn.neg (AlgRatFn.mul pFn (AlgRatFn.mul s.b s.b)))
        let nE := AlgRatFn.toExpr (AlgRatFn.neg N) v
        let partner : AlgSqrtFn := ⟨p, AlgRatFn.neg s.a, s.b⟩
        let lnN :=
          match AlgNum.ofExpr? (simplify nE) with
          | some _ => zero
          | none => ln nE
        simplify (sub lnN (ln (AlgSqrtFn.toExpr partner v)))
  | add a b => add (canonLnWalk a p v) (canonLnWalk b p v)
  | mul a b => mul (canonLnWalk a p v) (canonLnWalk b p v)
  | pow a b => pow (canonLnWalk a p v) b
  | _ => e

def finishEuler (F : Expr) (p : AlgPoly) (v : String) : Expr :=
  let F := simplify (canonLnWalk (simplify F) p v)
  match AlgSqrtFn.ofExpr? F v p with
  | some u => simplify (AlgSqrtFn.toExpr u v)
  | none => F

/-- Collect `ln` arguments (to clear denominators from F'). -/
partial def lnArgs : Expr → List Expr
  | ln u => [u]
  | add a b | mul a b => lnArgs a ++ lnArgs b
  | pow a _ => lnArgs a
  | _ => []

/-- Fast zero test after clearing `√p` and log denominators. -/
def cheapVerify (F f : Expr) (p : AlgPoly) (v : String) : Bool :=
  let F := simplify F
  let f := simplify f
  let err := sub (diff F v) f
  let s := sqrt (AlgPoly.toExpr p v)
  let cleared := (s :: lnArgs F).foldl (fun acc t => mul acc t) err
  let cleared := simplify cleared
  let algZero (e : Expr) : Bool :=
    match AlgSqrtFn.ofExpr? e v p with
    | some u => u.a.num.isZero && u.b.num.isZero
    | none => isZeroExpr e v
  isZeroExpr err v
    || equivNF (diff F v) f v
    || algZero (mul err s)
    || algZero cleared

def finishChecked (F : Expr) (f : Expr) (p : AlgPoly) (v : String) : Option Expr :=
  let F := finishEuler F p v
  if cheapVerify F f p v then some F else none

/-- Linear `p = m x + k`: `t = √p`, `x = (t² − k)/m`. -/
def eulerLinear (A B : AlgRatFn) (p : AlgPoly) (v : String) : Option Expr :=
  let m := AlgPoly.coeff p 1
  let k := AlgPoly.coeff p 0
  if m.isZero then none
  else
    let t := var eulerTName
    let xOfT := div (sub (pow t (ofInt 2)) (AlgNum.toExpr k)) (AlgNum.toExpr m)
    let yOfT := t
    let tBack := sqrt (AlgPoly.toExpr p v)
    runEulerSubst A B v eulerTName xOfT yOfT tBack

/-- Euler I: `√p = √a·x + t` when `√a ∈ K`. -/
def eulerQuadI (A B : AlgRatFn) (a b c : AlgNum) (p : AlgPoly) (v : String) :
    Option Expr :=
  match AlgNum.sqrt? a with
  | none => none
  | some α =>
    if α.isZero then none
    else
      let t := var eulerTName
      let αE := AlgNum.toExpr α
      let twoαt := mul (ofInt 2) (mul αE t)
      let xOfT :=
        div (sub (pow t (ofInt 2)) (AlgNum.toExpr c))
          (sub (AlgNum.toExpr b) twoαt)
      let yOfT := add (mul αE xOfT) t
      let tBack := sub (sqrt (AlgPoly.toExpr p v)) (mul αE (var v))
      runEulerSubst A B v eulerTName xOfT yOfT tBack

/-- Euler II: `√p = x t + √c` when `√c ∈ K`. -/
def eulerQuadII (A B : AlgRatFn) (a b c : AlgNum) (p : AlgPoly) (v : String) :
    Option Expr :=
  match AlgNum.sqrt? c with
  | none => none
  | some γ =>
    let t := var eulerTName
    let γE := AlgNum.toExpr γ
    let xOfT :=
      div (sub (mul (ofInt 2) (mul γE t)) (AlgNum.toExpr b))
        (sub (AlgNum.toExpr a) (pow t (ofInt 2)))
    let yOfT := add (mul t xOfT) γE
    let tBack := div (sub (sqrt (AlgPoly.toExpr p v)) γE) (var v)
    runEulerSubst A B v eulerTName xOfT yOfT tBack

/-- Linear roots of a quadratic, if it splits over K. -/
def quadLinearRoots? (p : AlgPoly) : Option (AlgNum × AlgNum) :=
  let (_c, fs) := AlgPoly.factorOverK p
  let ls := fs.filter (fun f => f.deg == 1)
  let rs :=
    ls.foldl (fun acc f =>
      let r := AlgNum.neg (AlgPoly.coeff (AlgPoly.monic f) 0)
      if acc.any (AlgNum.beq r) then acc else acc ++ [r]) []
  match rs with
  | [r1, r2] => if AlgNum.beq r1 r2 then none else some (r1, r2)
  | _ => none

/-- Euler III: `√p = t (x − α)` when `p = a(x−α)(x−β)`. -/
def eulerQuadIII (A B : AlgRatFn) (a : AlgNum) (p : AlgPoly) (v : String) :
    Option Expr :=
  match quadLinearRoots? p with
  | none => none
  | some (r1, r2) =>
    let t := var eulerTName
    let aE := AlgNum.toExpr a
    let r1E := AlgNum.toExpr r1
    let r2E := AlgNum.toExpr r2
    let xOfT :=
      div (sub (mul r1E (pow t (ofInt 2))) (mul aE r2E))
        (sub (pow t (ofInt 2)) aE)
    let yOfT := mul t (sub xOfT r1E)
    let tBack := div (sqrt (AlgPoly.toExpr p v)) (sub (var v) r1E)
    runEulerSubst A B v eulerTName xOfT yOfT tBack

/-- Euler substitution for a quadratic radical. -/
def eulerQuadratic (A B : AlgRatFn) (p : AlgPoly) (v : String) : Option Expr :=
  if p.deg != 2 then none
  else
    let a := AlgPoly.coeff p 2
    let b := AlgPoly.coeff p 1
    let c := AlgPoly.coeff p 0
    match eulerQuadI A B a b c p v with
    | some F => some F
    | none =>
      match eulerQuadII A B a b c p v with
      | some F => some F
      | none => eulerQuadIII A B a p v

/-- ∫ dx / √p  via Euler, then canonicalize logarithms. -/
def integrateInvSqrt (p : AlgPoly) (v : String) (f : Expr) : Option Expr :=
  let B := AlgRatFn.canceled ⟨AlgPoly.one, p⟩
  let go : Option Expr :=
    if p.deg == 1 then eulerLinear AlgRatFn.zero B p v
    else eulerQuadratic AlgRatFn.zero B p v
  match go with
  | none => none
  | some F => finishChecked F f p v

/-- ∫ √p dx: linear Euler, or quadratic reduction to ∫ 1/√p. -/
def integratePureSqrt (p : AlgPoly) (v : String) (f : Expr) : Option Expr :=
  if p.deg == 1 then
    match eulerLinear AlgRatFn.zero (AlgRatFn.ofPoly AlgPoly.one) p v with
    | some F => finishChecked F f p v
    | none => none
  else if p.deg == 2 then
    let a := AlgPoly.coeff p 2
    let b := AlgPoly.coeff p 1
    let c := AlgPoly.coeff p 0
    let fourA := AlgNum.scale (RatConst.ofInt 4) a
    if fourA.isZero then none
    else
      match integrateInvSqrt p v (div one (sqrt (AlgPoly.toExpr p v))) with
      | none => none
      | some I =>
        let s := sqrt (AlgPoly.toExpr p v)
        let twoA := AlgNum.scale (RatConst.ofInt 2) a
        let eightA := AlgNum.scale (RatConst.ofInt 8) a
        let lin := add (mul (AlgNum.toExpr twoA) (var v)) (AlgNum.toExpr b)
        let term1 := div (mul lin s) (AlgNum.toExpr fourA)
        let disc4 :=
          AlgNum.sub (AlgNum.mul fourA c) (AlgNum.mul b b)
        let term2 := mul (div (AlgNum.toExpr disc4) (AlgNum.toExpr eightA)) I
        finishChecked (simplify (add term1 term2)) f p v
  else none

/-- True when `u = 0 + 1·√p`. -/
def isPureSqrt (u : AlgSqrtFn) : Bool :=
  u.a.num.isZero && u.b.den.isOne && u.b.num.isOne

/-- True when `u = 0 + (1/p)·√p` i.e. `1/√p`. -/
def isInvSqrt (u : AlgSqrtFn) (p : AlgPoly) : Bool :=
  u.a.num.isZero && u.b.num.isOne && (AlgPoly.monic u.b.den == AlgPoly.monic p)

/--
  Integrate `e` if it lies in K(v)(√p) with deg p ∈ {1,2}.
-/
def integrateAlgSqrt? (e : Expr) (v : String := "x") : Option Expr :=
  let e := simplify e
  match uniqueQuadKernel? e v with
  | none => none
  | some p =>
    match AlgSqrtFn.ofExpr? e v p with
    | none => none
    | some u =>
      if u.b.num.isZero then
        integrateRationalExpr (AlgRatFn.toExpr u.a v) v
      else if isPureSqrt u then
        integratePureSqrt p v e
      else if isInvSqrt u p then
        integrateInvSqrt p v e
      else
        let raw :=
          if p.deg == 1 then eulerLinear u.a u.b p v
          else if p.deg == 2 then eulerQuadratic u.a u.b p v
          else none
        match raw with
        | none => none
        | some F => finishChecked F e p v

/-! ### Compile-time smoke tests (kept small; full suite lives in Regression) -/

#guard
  match uniqueQuadKernel? (sqrt (Expr.add (Expr.var "x") Expr.one)) "x" with
  | some p => p.deg == 1
  | none => false

#guard
  (integrateAlgSqrt? (sqrt (Expr.add (Expr.var "x") Expr.one)) "x").isSome

#guard
  (integrateAlgSqrt? (div Expr.one (sqrt (Expr.add (pow (Expr.var "x") (ofInt 2)) Expr.one))) "x").isSome

end Taschenrechner
