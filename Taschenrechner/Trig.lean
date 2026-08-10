/-
  Trigonometric preprocessing for the Risch pipeline.

  Before the main transcendental cases run, we:
  1. Rewrite `tan` as `sin/cos`
  2. Power-reduce `sin²` / `cos²`
  3. Apply product-to-sum identities (`sin·cos`, `sin·sin`, `cos·cos`)
  4. Integrate pure `sin`/`cos`/`tan` of **linear** arguments (ax+b)
     as part of the Risch elementary class (same closed forms as classical tables)

  Non-linear arguments (e.g. `cos(x²)`) are left for reverse-chain / heuristics.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify

namespace Taschenrechner

open Expr

/-- Match `a·v + b` with rational `a,b` (b may be 0). -/
partial def linearForm (e : Expr) (v : String) : Option (RatConst × RatConst) :=
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
    match linearForm a v, asRatConst? b with
    | some (ca, cb), some rb => some (ca, cb + rb)
    | _, _ =>
      match asRatConst? a, linearForm b v with
      | some ra, some (ca, cb) => some (ca, cb + ra)
      | _, _ =>
        match linearForm a v, linearForm b v with
        | some (ca1, cb1), some (ca2, cb2) => some (ca1 + ca2, cb1 + cb2)
        | _, _ => none
  | const _ => none
  | _ => none
where
  asRatConst? : Expr → Option RatConst
    | const r => CplxConst.toRat? r
    | _ => none

/-- True if `e` is linear in `v` (or constant). -/
def isLinearIn (e : Expr) (v : String) : Bool :=
  match linearForm e v with
  | some _ => true
  | none =>
    match simplify e with
    | const _ => true
    | _ => false

/-! ### Product-to-sum and power reduction -/

/-- `sin A cos B = (sin(A+B) + sin(A-B)) / 2` -/
def prodSinCos (A B : Expr) : Expr :=
  let sp := Expr.sin (Expr.add A B)
  let sm := Expr.sin (Expr.sub A B)
  Expr.div (Expr.add sp sm) (2 : Expr)

/-- `cos A sin B = (sin(A+B) - sin(A-B)) / 2` -/
def prodCosSin (A B : Expr) : Expr :=
  let sp := Expr.sin (Expr.add A B)
  let sm := Expr.sin (Expr.sub A B)
  Expr.div (Expr.sub sp sm) (2 : Expr)

/-- `sin A sin B = (cos(A-B) - cos(A+B)) / 2` -/
def prodSinSin (A B : Expr) : Expr :=
  let cm := Expr.cos (Expr.sub A B)
  let cp := Expr.cos (Expr.add A B)
  Expr.div (Expr.sub cm cp) (2 : Expr)

/-- `cos A cos B = (cos(A+B) + cos(A-B)) / 2` -/
def prodCosCos (A B : Expr) : Expr :=
  let cp := Expr.cos (Expr.add A B)
  let cm := Expr.cos (Expr.sub A B)
  Expr.div (Expr.add cp cm) (2 : Expr)

/-- `sin² u = (1 - cos(2u)) / 2` -/
def sinSq (u : Expr) : Expr :=
  Expr.div (Expr.sub (1 : Expr) (Expr.cos (Expr.mul (2 : Expr) u))) (2 : Expr)

/-- `cos² u = (1 + cos(2u)) / 2` -/
def cosSq (u : Expr) : Expr :=
  Expr.div (Expr.add (1 : Expr) (Expr.cos (Expr.mul (2 : Expr) u))) (2 : Expr)

/-- One bottom-up trig rewrite pass (no integration). -/
partial def trigRewrite1 (e : Expr) : Expr :=
  match e with
  | const r => const r
  | var n => var n
  | add a b => add (trigRewrite1 a) (trigRewrite1 b)
  | mul a b =>
    let a := trigRewrite1 a
    let b := trigRewrite1 b
    match a, b with
    | sin A, cos B => prodSinCos A B
    | cos A, sin B => prodCosSin A B
    | sin A, sin B => prodSinSin A B
    | cos A, cos B => prodCosCos A B
    -- const * (trig product already handled by simplify order — peel one layer)
    | mul (const c) (sin A), cos B =>
      mul (const c) (prodSinCos A B)
    | mul (const c) (cos A), sin B =>
      mul (const c) (prodCosSin A B)
    | sin A, mul (const c) (cos B) =>
      mul (const c) (prodSinCos A B)
    | cos A, mul (const c) (sin B) =>
      mul (const c) (prodCosSin A B)
    | _, _ => mul a b
  | pow a b =>
    let a := trigRewrite1 a
    let b := trigRewrite1 b
    match a, b with
    | sin u, const r =>
      if r == CplxConst.ofInt 2 then sinSq u
      else if r.isOne then sin u
      else pow a b
    | cos u, const r =>
      if r == CplxConst.ofInt 2 then cosSq u
      else if r.isOne then cos u
      else pow a b
    | _, _ => pow a b
  | sin a => sin (trigRewrite1 a)
  | cos a => cos (trigRewrite1 a)
  | tan a =>
    -- tan u = sin u / cos u
    let a := trigRewrite1 a
    Expr.div (sin a) (cos a)
  | exp a => exp (trigRewrite1 a)
  | ln a => ln (trigRewrite1 a)
  | atan a => atan (trigRewrite1 a)
  | re a => re (trigRewrite1 a)
  | im a => im (trigRewrite1 a)
  | conj a => conj (trigRewrite1 a)
  | eq a b => eq (trigRewrite1 a) (trigRewrite1 b)
  | mat rows => mat (rows.map (fun row => row.map trigRewrite1))

/-- Iterate trig rewrites to a fixed point (bounded). -/
def trigPreprocess (e : Expr) (maxIters : Nat := 8) : Expr :=
  let rec go (n : Nat) (e : Expr) : Expr :=
    match n with
    | 0 => e
    | n'+1 =>
      let e' := simplify (trigRewrite1 e)
      if e' == e then e else go n' e'
  go maxIters (simplify e)

/-! ### Linear-argument elementary integrals (Risch trig extension) -/

/--
  ∫ f(ax+b) dx for f ∈ {sin, cos, tan} and rational a ≠ 0.
  Returns antiderivative in terms of the original inner expression when useful.
-/
partial def integrateLinearTrig (e : Expr) (v : String) : Option Expr :=
  let e := simplify e
  let tryLin (inner : Expr) (antiAt : Expr → Expr) : Option Expr :=
    match linearForm inner v with
    | some (a, _b) =>
      if a.isZero then none
      else
        match RatConst.inv a with
        | some invA => some (simplify (mul (ofRat invA) (antiAt inner)))
        | none => none
    | none =>
      if inner == var v then some (simplify (antiAt (var v)))
      else none
  match e with
  | sin inner => tryLin inner fun u => neg (cos u)
  | cos inner => tryLin inner fun u => sin u
  | tan inner => tryLin inner fun u => neg (ln (cos u))
  | mul (const c) body =>
    match integrateLinearTrig body v with
    | some F => some (simplify (mul (const c) F))
    | none => none
  | mul body (const c) =>
    match integrateLinearTrig body v with
    | some F => some (simplify (mul (const c) F))
    | none => none
  | _ => none

/--
  Full trig front-end for Risch: preprocess, then try linear-trig integration
  on the whole expression or summands.
-/
partial def rischTrig (e : Expr) (v : String) : Option Expr :=
  let e := trigPreprocess e
  match integrateLinearTrig e v with
  | some F => some F
  | none =>
    -- Linearity after product-to-sum: sin(2x)/2 + …
    match e with
    | add a b =>
      match rischTrig a v, rischTrig b v with
      | some A, some B => some (simplify (add A B))
      | _, _ => none
    | mul (const c) body =>
      match rischTrig body v with
      | some F => some (simplify (mul (const c) F))
      | none => none
    | mul body (const c) =>
      match rischTrig body v with
      | some F => some (simplify (mul (const c) F))
      | none => none
    | _ => none

end Taschenrechner
