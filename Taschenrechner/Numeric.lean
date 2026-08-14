/-
  Floating-point numeric evaluation.

  * `N(e)` / `N(e, digits)` — approximate a ground expression to a rounded rational
  * Decimals parse as exact rationals; many print back as decimals (den | 2^a 5^b)
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Complex
import Taschenrechner.Eval

namespace Taschenrechner

open Expr

/-- Convert `Int` to `Float`. -/
def intToFloat (n : Int) : Float :=
  if n ≥ 0 then n.toNat.toFloat else -(n.natAbs.toFloat)

/-- Convert rational to `Float`. -/
def ratToFloat (r : RatConst) : Float :=
  intToFloat r.num / r.den.toFloat

/-- Convert complex rational to real/imag floats. -/
def cplxToFloats (c : CplxConst) : Float × Float :=
  (ratToFloat c.re, ratToFloat c.im)

/-- Round a non-negative float to nearest `Nat` (clamped). -/
def floatToNatRound (x : Float) : Nat :=
  if x < 0 then 0
  else if x.isNaN || x.isInf then 0
  else (Float.floor (x + 0.5)).toUInt64.toNat

/-- Round float to nearest `Int`. -/
def floatToIntRound (x : Float) : Int :=
  if x.isNaN then 0
  else if x ≥ 0 then (floatToNatRound x : Int)
  else -((floatToNatRound (-x) : Int))

/-- `10^n` as Float (n small). -/
def tenPowFloat (n : Nat) : Float :=
  Float.pow 10.0 n.toFloat

/-- Round `x` to `digits` digits after the decimal point as a rational. -/
def floatToRat (x : Float) (digits : Nat) : RatConst :=
  let digits := min digits 12  -- stay within float / UInt64 comfort
  if x.isNaN then RatConst.zero
  else if x.isInf then
    -- cannot represent ∞ as RatConst; use a large sentinel? better zero + error upstream
    RatConst.zero
  else
    let scale := tenPowFloat digits
    let scaled := x * scale
    let n := floatToIntRound scaled
    let den := Nat.pow 10 digits
    RatConst.normalize ⟨n, den⟩

/-- Lanczos approximation of Γ(z) for real `z` (reflection for z < 1/2). -/
partial def gammaFloat (z : Float) : Option Float :=
  if z.isNaN || z.isInf then none
  else if z < 0.5 then
    let pi := Float.acos (-1.0)
    let s := Float.sin (pi * z)
    if Float.abs s < 1e-15 then none
    else
      match gammaFloat (1.0 - z) with
      | some g => some (pi / (s * g))
      | none => none
  else
    let z := z - 1.0
    let p : Array Float := #[
      0.99999999999980993,
      676.5203681218851,
      -1259.1392167224028,
      771.32342877765313,
      -176.61502916214059,
      12.507343278686905,
      -0.13857109526572012,
      9.9843695780195716e-6,
      1.5056327351493116e-7]
    let x :=
      Id.run do
        let mut acc := p[0]!
        for i in [1:p.size] do
          acc := acc + p[i]! / (z + i.toFloat)
        pure acc
    let t := z + 7.5
    let pi := Float.acos (-1.0)
    some (Float.sqrt (2.0 * pi) * Float.pow t (z + 0.5) * Float.exp (-t) * x)

/--
  Numeric evaluation of a ground expression to real/imag floats.
  Supports rationals, +, −, *, /, ^, trig, exp, ln, sqrt, inverse trig,
  sec/csc/cot, factorial/gamma, floor, piecewise, re, im, conj.
-/
partial def evalFloats? (e : Expr) : Option (Float × Float) :=
  match simplify e with
  | const c => some (cplxToFloats c)
  | var v =>
    if Expr.isPiName v then some (Float.acos (-1.0), 0)
    else none
  | add a b =>
    match evalFloats? a, evalFloats? b with
    | some (ar, ai), some (br, bi) => some (ar + br, ai + bi)
    | _, _ => none
  | mul a b =>
    match evalFloats? a, evalFloats? b with
    | some (ar, ai), some (br, bi) =>
      -- (ar+ai i)(br+bi i)
      some (ar * br - ai * bi, ar * bi + ai * br)
    | _, _ => none
  | pow a b =>
    match evalFloats? a, evalFloats? b with
    | some (ar, ai), some (br, bi) =>
      if ai == 0 && bi == 0 then
        -- real^real
        if ar < 0 then
          -- integer power only for negative base
          let brR := floatToIntRound br
          if Float.abs (br - intToFloat brR) < 1e-9 then
            let af := ar
            some (Float.pow af (intToFloat brR), 0)
          else none
        else
          some (Float.pow ar br, 0)
      else if ai == 0 && bi == 0 then some (Float.pow ar br, 0)
      else none  -- complex power not supported
    | _, _ => none
  | sin a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.sin r, 0) else none
    | none => none
  | cos a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.cos r, 0) else none
    | none => none
  | tan a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.tan r, 0) else none
    | none => none
  | sinh a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.sinh r, 0) else none
    | none => none
  | cosh a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.cosh r, 0) else none
    | none => none
  | tanh a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.tanh r, 0) else none
    | none => none
  | abs a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 then some (Float.abs r, 0)
      else some (Float.sqrt (r * r + i * i), 0)
    | none => none
  | exp a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 then some (Float.exp r, 0)
      else
        -- exp(x+iy) = e^x (cos y + i sin y)
        let er := Float.exp r
        some (er * Float.cos i, er * Float.sin i)
    | none => none
  | ln a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 && r > 0 then some (Float.log r, 0)
      else if i == 0 && r < 0 then
        -- principal log: ln|r| + i π
        some (Float.log (Float.abs r), Float.acos (-1.0))  -- π
      else
        -- Log of complex: ln|z| + i arg
        let mod := Float.sqrt (r * r + i * i)
        if mod == 0 then none
        else some (Float.log mod, Float.atan2 i r)
    | none => none
  | atan a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.atan r, 0) else none
    | none => none
  | asin a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 && r ≥ -1 && r ≤ 1 then some (Float.asin r, 0) else none
    | none => none
  | acos a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 && r ≥ -1 && r ≤ 1 then some (Float.acos r, 0) else none
    | none => none
  | Expr.re a =>
    match evalFloats? a with
    | some (r, _) => some (r, 0)
    | none => none
  | Expr.im a =>
    match evalFloats? a with
    | some (_, i) => some (i, 0)
    | none => none
  | Expr.conj a =>
    match evalFloats? a with
    | some (r, i) => some (r, -i)
    | none => none
  | sec a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 then
        let c := Float.cos r
        if Float.abs c < 1e-15 then none else some (1.0 / c, 0)
      else none
    | none => none
  | csc a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 then
        let s := Float.sin r
        if Float.abs s < 1e-15 then none else some (1.0 / s, 0)
      else none
    | none => none
  | cot a =>
    match evalFloats? a with
    | some (r, i) =>
      if i == 0 then
        let s := Float.sin r
        if Float.abs s < 1e-15 then none else some (Float.cos r / s, 0)
      else none
    | none => none
  | factorial a =>
    match evalFloats? a with
    | some (r, i) =>
      if i != 0 then none
      else if r ≥ 0 && Float.abs (r - Float.floor r) < 1e-9 then
        let n := Float.floor r |>.toUInt64.toNat
        if n ≤ 20 then some ((factNat n).toFloat, 0)
        else
          match gammaFloat (r + 1.0) with
          | some g => some (g, 0)
          | none => none
      else
        match gammaFloat (r + 1.0) with
        | some g => some (g, 0)
        | none => none
    | none => none
  | gamma a =>
    match evalFloats? a with
    | some (r, i) =>
      if i != 0 then none
      else
        match gammaFloat r with
        | some g => some (g, 0)
        | none => none
    | none => none
  | floor a =>
    match evalFloats? a with
    | some (r, i) => if i == 0 then some (Float.floor r, 0) else none
    | none => none
  | Expr.ite c t e =>
    let pick (b : Bool) := if b then evalFloats? t else evalFloats? e
    match c with
    | eq a b =>
      match evalFloats? a, evalFloats? b with
      | some (ar, ai), some (br, bi) =>
        pick (Float.abs (ar - br) < 1e-9 && Float.abs (ai - bi) < 1e-9)
      | _, _ => none
    | lt a b =>
      match evalFloats? a, evalFloats? b with
      | some (ar, ai), some (br, bi) =>
        if ai == 0 && bi == 0 then pick (ar < br) else none
      | _, _ => none
    | le a b =>
      match evalFloats? a, evalFloats? b with
      | some (ar, ai), some (br, bi) =>
        if ai == 0 && bi == 0 then pick (ar ≤ br) else none
      | _, _ => none
    | _ => none
  | _ => none

/-- Numeric sqrt for non-negative reals (and principal for negatives → i√). -/
partial def evalFloatsWithSqrt? (e : Expr) : Option (Float × Float) :=
  match simplify e with
  | pow base (const c) =>
    match CplxConst.toRat? c with
    | some q =>
      if q == ⟨1, 2⟩ then
        match evalFloatsWithSqrt? base with
        | some (r, i) =>
          if i == 0 then
            if r ≥ 0 then some (Float.sqrt r, 0)
            else some (0, Float.sqrt (-r))
          else none
        | none => none
      else evalFloats? e
    | none => evalFloats? e
  | e =>
    match evalFloats? e with
    | some z => some z
    | none =>
      -- fallback: expand common ops that simplify might leave as structure
      match e with
      | add a b =>
        match evalFloatsWithSqrt? a, evalFloatsWithSqrt? b with
        | some (ar, ai), some (br, bi) => some (ar + br, ai + bi)
        | _, _ => none
      | mul a b =>
        match evalFloatsWithSqrt? a, evalFloatsWithSqrt? b with
        | some (ar, ai), some (br, bi) =>
          some (ar * br - ai * bi, ar * bi + ai * br)
        | _, _ => none
      | _ => none

/-- Build Expr from rounded real/imag floats. -/
def floatsToExpr (reF imF : Float) (digits : Nat) : Expr :=
  let r := floatToRat reF digits
  let i := floatToRat imF digits
  if i.isZero then ofRat r
  else if r.isZero then
    if i.isOne then I
    else if i.isNegOne then neg I
    else mul (ofRat i) I
  else
    simplify (add (ofRat r) (mul (ofRat i) I))

/--
  Numerically evaluate `e` to `digits` decimal places (default 6).
  Returns a rational (or complex rational) approximation as an `Expr`.
-/
def numericEval (e : Expr) (digits : Nat := 6) : Except String Expr :=
  let e := simplify e
  -- Prefer exact ℚ(i) when fully ground and elementary-constant-free
  match eval? e with
  | some c =>
    if c.im.isZero then pure (ofRat c.re)
    else pure (const c)
  | none =>
    match evalFloatsWithSqrt? e with
    | none => throw "N: could not numerically evaluate (free variables or unsupported ops?)"
    | some (reF, imF) =>
      if reF.isNaN || imF.isNaN then
        throw "N: result is NaN"
      else if reF.isInf || imF.isInf then
        throw "N: result is infinite"
      else
        pure (floatsToExpr reF imF digits)

/-- Alias used by the parser. -/
def N (e : Expr) (digits : Nat := 6) : Except String Expr :=
  numericEval e digits

/-- Format a float pair as a decimal string (for diagnostics / CLI). -/
def formatFloats (reF imF : Float) (digits : Nat) : String :=
  let e := floatsToExpr reF imF digits
  Expr.toString e

end Taschenrechner
