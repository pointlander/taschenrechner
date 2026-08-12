/-
  Identity rewrite table applied during simplification.

  Rules fire bottom-up at each node after structural simplify. Keep rules
  local and terminating (no expansion loops).
-/
import Taschenrechner.Expr

namespace Taschenrechner

open Expr

private def isTwo (c : CplxConst) : Bool :=
  c.isReal && c.re == RatConst.ofInt 2

private def isEvenInt (c : CplxConst) : Bool :=
  match CplxConst.toRat? c with
  | some q => q.den == 1 && q.num % 2 == 0 && q.num > 0
  | none => false

/-- Absolute value of a real rational constant. -/
private def ratAbs (r : RatConst) : RatConst :=
  if r.num < 0 then RatConst.neg r else r

/-- One local rewrite attempt at the root of `e` (children already rewritten). -/
def rewriteRoot (e : Expr) : Option Expr :=
  match e with
  -- trig Pythagorean: sin²u + cos²u → 1  (and cos²+sin²)
  | add a b =>
    match a, b with
    | pow (sin u) (const r), pow (cos v) (const s) =>
      if isTwo r && isTwo s && u == v then some one else none
    | pow (cos u) (const r), pow (sin v) (const s) =>
      if isTwo r && isTwo s && u == v then some one else none
    -- cosh²u + (-1)·sinh²u → 1
    | pow (cosh u) (const r), mul (const c) (pow (sinh v) (const s)) =>
      if isTwo r && isTwo s && c.isNegOne && u == v then some one else none
    | mul (const c) (pow (sinh u) (const r)), pow (cosh v) (const s) =>
      if isTwo r && isTwo s && c.isNegOne && u == v then some one else none
    | _, _ => none
  -- exp(a)*exp(b) → exp(a+b)
  | mul (exp a) (exp b) => some (exp (add a b))
  -- exp(0) already handled; ln(exp u) → u in simplify
  -- abs
  | abs (abs u) => some (abs u)
  | abs (mul (const c) u) =>
    if c.isNegOne then some (abs u)
    else if c.isReal && c.re.num < 0 then
      some (mul (ofRat (ratAbs c.re)) (abs u))
    else if c.isReal then
      some (mul (ofRat (ratAbs c.re)) (abs u))
    else none
  | abs (const c) =>
    if c.isReal then some (ofRat (ratAbs c.re)) else none
  | abs (pow u (const r)) =>
    if isTwo r then some (pow u (ofInt 2))  -- |u|² → u² (real convention)
    else if isEvenInt r then
      match CplxConst.toRat? r with
      | some q => some (pow u (ofInt q.num))  -- |u|^{2k} → u^{2k}
      | none => none
    else none
  -- |u|² written as abs(u)^2
  | pow (abs u) (const r) =>
    if isTwo r then some (pow u (ofInt 2)) else none
  -- hyperbolics of zero / negatives
  | sinh (const c) => if c.isZero then some zero else none
  | cosh (const c) => if c.isZero then some one else none
  | tanh (const c) => if c.isZero then some zero else none
  | sinh (mul (const c) u) =>
    if c.isNegOne then some (neg (sinh u)) else none
  | cosh (mul (const c) u) =>
    if c.isNegOne then some (cosh u) else none
  | tanh (mul (const c) u) =>
    if c.isNegOne then some (neg (tanh u)) else none
  -- sin/cos of zero already in simplify1
  | sin (mul (const c) u) =>
    if c.isNegOne then some (neg (sin u)) else none
  | cos (mul (const c) u) =>
    if c.isNegOne then some (cos u) else none
  | tan (mul (const c) u) =>
    if c.isNegOne then some (neg (tan u)) else none
  -- exp(-ln u) → 1/u ; exp(k·ln u) → u^k
  | exp (mul (const c) (ln u)) =>
    match CplxConst.toRat? c with
    | some q =>
      if q == RatConst.negOne then some (div one u)
      else if q.den == 1 then some (pow u (ofInt q.num))
      else none
    | none => none
  | _ => none

/-- Bottom-up rewrite pass (one sweep). -/
partial def rewrite1 (e : Expr) : Expr :=
  let e :=
    match e with
    | add a b => add (rewrite1 a) (rewrite1 b)
    | mul a b => mul (rewrite1 a) (rewrite1 b)
    | pow a b => pow (rewrite1 a) (rewrite1 b)
    | sin a => sin (rewrite1 a)
    | cos a => cos (rewrite1 a)
    | tan a => tan (rewrite1 a)
    | sinh a => sinh (rewrite1 a)
    | cosh a => cosh (rewrite1 a)
    | tanh a => tanh (rewrite1 a)
    | exp a => exp (rewrite1 a)
    | ln a => ln (rewrite1 a)
    | atan a => atan (rewrite1 a)
    | asin a => asin (rewrite1 a)
    | acos a => acos (rewrite1 a)
    | abs a => abs (rewrite1 a)
    | re a => re (rewrite1 a)
    | im a => im (rewrite1 a)
    | conj a => conj (rewrite1 a)
    | eq a b => eq (rewrite1 a) (rewrite1 b)
    | lt a b => lt (rewrite1 a) (rewrite1 b)
    | le a b => le (rewrite1 a) (rewrite1 b)
    | mat rows => mat (rows.map fun row => row.map rewrite1)
    | e => e
  match rewriteRoot e with
  | some e' => e'
  | none => e

/-- Iterate rewrites (bounded). -/
def rewrite (e : Expr) (maxIters : Nat := 16) : Expr :=
  let rec go (n : Nat) (e : Expr) : Expr :=
    match n with
    | 0 => e
    | n'+1 =>
      let e' := rewrite1 e
      if e' == e then e else go n' e'
  go maxIters e

/-- Hyperbolic ↔ exponential (expand form). -/
partial def expandHyperbolic (e : Expr) : Expr :=
  match e with
  | sinh u =>
    let u := expandHyperbolic u
    div (sub (exp u) (exp (neg u))) (ofInt 2)
  | cosh u =>
    let u := expandHyperbolic u
    div (add (exp u) (exp (neg u))) (ofInt 2)
  | tanh u =>
    let u := expandHyperbolic u
    let sh := div (sub (exp u) (exp (neg u))) (ofInt 2)
    let ch := div (add (exp u) (exp (neg u))) (ofInt 2)
    div sh ch
  | add a b => add (expandHyperbolic a) (expandHyperbolic b)
  | mul a b => mul (expandHyperbolic a) (expandHyperbolic b)
  | pow a b => pow (expandHyperbolic a) (expandHyperbolic b)
  | sin a => sin (expandHyperbolic a)
  | cos a => cos (expandHyperbolic a)
  | tan a => tan (expandHyperbolic a)
  | exp a => exp (expandHyperbolic a)
  | ln a => ln (expandHyperbolic a)
  | atan a => atan (expandHyperbolic a)
  | asin a => asin (expandHyperbolic a)
  | acos a => acos (expandHyperbolic a)
  | abs a => abs (expandHyperbolic a)
  | re a => re (expandHyperbolic a)
  | im a => im (expandHyperbolic a)
  | conj a => conj (expandHyperbolic a)
  | eq a b => eq (expandHyperbolic a) (expandHyperbolic b)
  | lt a b => lt (expandHyperbolic a) (expandHyperbolic b)
  | le a b => le (expandHyperbolic a) (expandHyperbolic b)
  | mat rows => mat (rows.map fun row => row.map expandHyperbolic)
  | e => e

end Taschenrechner
