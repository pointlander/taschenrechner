/-
  Complex analysis helpers on the expression AST.

  * Constants live in `ℚ(i)` via `CplxConst`
  * `eulerExpand` applies Euler's formula to `exp` of complex-linear args
  * `cis` / polar helpers for building complex values
-/
import Taschenrechner.Simplify
import Taschenrechner.Diff

namespace Taschenrechner

open Expr

/-- `cis(θ) = cos θ + i sin θ`. -/
def cis (θ : Expr) : Expr :=
  Expr.add (Expr.cos θ) (Expr.mul Expr.I (Expr.sin θ))

/--
  Match `α + β·i` where `α, β` are real expressions independent of `i`
  (constants may already be folded into `CplxConst`).
-/
partial def matchComplexLinear (e : Expr) : Option (Expr × Expr) :=
  let e := simplify e
  match e with
  | const c => some (ofRat c.re, ofRat c.im)
  | mul (const c) rest =>
    if c.isPureI then
      -- i * rest  (rest treated as real imag part)
      some (zero, simplify (mul (ofRat c.im) rest))
    else if c.isReal then
      match matchComplexLinear rest with
      | some (a, b) => some (simplify (mul (ofRat c.re) a), simplify (mul (ofRat c.re) b))
      | none => some (simplify (mul (ofRat c.re) rest), zero)
    else
      -- general complex coeff * rest (rest real)
      some (simplify (mul (ofRat c.re) rest), simplify (mul (ofRat c.im) rest))
  | mul rest (const c) => matchComplexLinear (mul (const c) rest)
  | add a b =>
    match matchComplexLinear a, matchComplexLinear b with
    | some (a1, b1), some (a2, b2) =>
      some (simplify (add a1 a2), simplify (add b1 b2))
    | some (a1, b1), none =>
      -- b real
      some (simplify (add a1 b), b1)
    | none, some (a2, b2) =>
      some (simplify (add a a2), b2)
    | none, none =>
      -- both real
      some (simplify (add a b), zero)
  | re _ | im _ | conj _ | sin _ | cos _ | tan _ | atan _ | ln _ | exp _ | var _ | pow _ _ =>
    -- treat as real
    some (e, zero)
  | eq _ _ => none
  | mat _ => none
  | _ => some (e, zero)

/--
  Euler expand: `exp(a + b i) → exp(a)·(cos b + i sin b)`.
  Applied bottom-up; real exponents unchanged.
-/
partial def eulerExpand1 (e : Expr) : Expr :=
  match e with
  | const c => const c
  | var v => var v
  | add a b => add (eulerExpand1 a) (eulerExpand1 b)
  | mul a b => mul (eulerExpand1 a) (eulerExpand1 b)
  | pow a b => pow (eulerExpand1 a) (eulerExpand1 b)
  | sin a => sin (eulerExpand1 a)
  | cos a => cos (eulerExpand1 a)
  | tan a => tan (eulerExpand1 a)
  | ln a => ln (eulerExpand1 a)
  | atan a => atan (eulerExpand1 a)
  | re a => re (eulerExpand1 a)
  | im a => im (eulerExpand1 a)
  | conj a => conj (eulerExpand1 a)
  | eq a b => eq (eulerExpand1 a) (eulerExpand1 b)
  | mat rows => mat (rows.map (fun row => row.map eulerExpand1))
  | exp a =>
    let a := eulerExpand1 a
    match matchComplexLinear a with
    | none => exp a
    | some (α, β) =>
      let βs := simplify β
      if βs == zero then exp α
      else
        -- exp(α)·(cos β + i sin β)
        let mag := if simplify α == zero then one else exp α
        simplify (mul mag (cis βs))

def eulerExpand (e : Expr) (maxIters : Nat := 8) : Expr :=
  let rec go (n : Nat) (e : Expr) : Expr :=
    match n with
    | 0 => e
    | n'+1 =>
      let e' := simplify (eulerExpand1 e)
      if e' == e then e else go n' e'
  go maxIters (simplify e)

/-! ### Complex exponentials under differentiation / integration -/

/--
  Match `α + β·v` with complex constant coefficients α, β ∈ ℚ(i).
  Returns `(α, β)`.
-/
partial def asCplxLinearIn (e : Expr) (v : String) : Option (CplxConst × CplxConst) :=
  let e := simplify e
  match e with
  | const c =>
    -- constant (no v): α = c, β = 0
    some (c, CplxConst.zero)
  | var name =>
    if name == v then some (CplxConst.zero, CplxConst.one) else none
  | mul (const c) (var name) =>
    if name == v then some (CplxConst.zero, c) else none
  | mul (var name) (const c) =>
    if name == v then some (CplxConst.zero, c) else none
  | add a b =>
    match asCplxLinearIn a v, asCplxLinearIn b v with
    | some (α1, β1), some (α2, β2) => some (α1 + α2, β1 + β2)
    | _, _ => none
  | _ => none

/--
  Match `r · exp(α + β v)` with r, α, β ∈ ℚ(i).
  Returns `(r, α, β)`.
-/
partial def matchExpCplxLinear (e : Expr) (v : String) : Option (CplxConst × CplxConst × CplxConst) :=
  let e := simplify e
  match e with
  | exp arg =>
    match asCplxLinearIn arg v with
    | some (α, β) =>
      if β.isZero then none  -- pure constant exp; outer handle
      else some (CplxConst.one, α, β)
    | none => none
  | mul (const c) rest =>
    match matchExpCplxLinear rest v with
    | some (_, α, β) => some (c, α, β)
    | none => none
  | mul rest (const c) =>
    matchExpCplxLinear (mul (const c) rest) v
  | _ => none

/--
  ∫ r · exp(α + β v) dv =
  * (r/β) · exp(α + β v)   if β ≠ 0
  * r · exp(α) · v         if β = 0
-/
def integrateExpCplxLinear (r α β : CplxConst) (v : String) : Option Expr :=
  let body :=
    exp (simplify (add (const α) (mul (const β) (var v))))
  if β.isZero then
    some (simplify (mul (mul (const r) (exp (const α))) (var v)))
  else
    match CplxConst.inv β with
    | none => none
    | some invβ =>
      some (simplify (mul (const (r * invβ)) body))

/-- Evaluate a constant complex expression to `CplxConst` when possible. -/
partial def evalCplx? (e : Expr) : Option CplxConst :=
  match simplify e with
  | const c => some c
  | add a b =>
    match evalCplx? a, evalCplx? b with
    | some ca, some cb => some (ca + cb)
    | _, _ => none
  | mul a b =>
    match evalCplx? a, evalCplx? b with
    | some ca, some cb => some (ca * cb)
    | _, _ => none
  | pow a (const r) =>
    match evalCplx? a, CplxConst.toRat? r with
    | some ca, some q =>
      if q.den == 1 then CplxConst.powInt ca q.num else none
    | _, _ => none
  | re a =>
    match evalCplx? a with
    | some c => some (CplxConst.ofRat c.re)
    | none => none
  | im a =>
    match evalCplx? a with
    | some c => some (CplxConst.ofRat c.im)
    | none => none
  | conj a =>
    match evalCplx? a with
    | some c => some (CplxConst.conj c)
    | none => none
  | _ => none

end Taschenrechner
