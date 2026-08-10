/-
  Symbolic limits.

  * Finite points for rationals (with L'Hôpital on 0/0)
  * ±∞ for rational functions via degree / leading coefficients
  * Continuous elementary substitution when the limit is ground
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Eval
import Taschenrechner.Normal
import Taschenrechner.Solve

namespace Taschenrechner

open Expr

/-! ### Limit points -/

inductive LimitPoint where
  | finite : Expr → LimitPoint
  | posInf
  | negInf
  deriving Repr, Inhabited

namespace LimitPoint

/-- Interpret an expression as a limit point (`oo` / `inf` / `∞` = +∞). -/
def ofExpr : Expr → LimitPoint
  | var name =>
    let n := name.toLower
    if n == "oo" || n == "inf" || n == "infty" || n == "infinity" || name == "∞" then
      .posInf
    else .finite (var name)
  | mul (const c) (var name) =>
    let n := name.toLower
    if n == "oo" || n == "inf" || n == "infty" || n == "infinity" || name == "∞" then
      if c.isZero then .finite zero
      else if c.isReal && c.re.num < 0 then .negInf
      else .posInf
    else .finite (mul (const c) (var name))
  | e =>
    -- (−1)·oo and similar after simplify
    match e with
    | mul (const c) rest =>
      match ofExpr rest with
      | .posInf => if c.isReal && c.re.num < 0 then .negInf else .posInf
      | .negInf => if c.isReal && c.re.num < 0 then .posInf else .negInf
      | .finite _ => .finite e
    | _ =>
      -- bare -oo often as mul negOne (var "oo")
      .finite e

def toString : LimitPoint → String
  | .finite e => s!"{e}"
  | .posInf => "+∞"
  | .negInf => "-∞"

instance : ToString LimitPoint where
  toString := toString

end LimitPoint

/-! ### Limit results -/

inductive LimitResult where
  /-- Finite limit value. -/
  | value : Expr → LimitResult
  /-- Diverges to ±∞ (`pos = true` means +∞). -/
  | infinity : (pos : Bool) → LimitResult
  /-- Could not decide. -/
  | undetermined : String → LimitResult
  deriving Repr, Inhabited

namespace LimitResult

def toExpr : LimitResult → Expr
  | .value e => e
  | .infinity true => var "∞"
  | .infinity false => Expr.neg (var "∞")
  | .undetermined _ => var "undetermined"

def toString : LimitResult → String
  | .value e => s!"{e}"
  | .infinity true => "+∞"
  | .infinity false => "-∞"
  | .undetermined msg => s!"undetermined ({msg})"

instance : ToString LimitResult where
  toString := toString

/-- For the parser: finite value or ±∞ as expressions; error on undetermined. -/
def toExpr? : LimitResult → Except String Expr
  | .value e => pure e
  | .infinity true => pure (var "∞")
  | .infinity false => pure (Expr.neg (var "∞"))
  | .undetermined msg => throw msg

end LimitResult

/-! ### Helpers -/

/-- Sign of a non-zero real rational: `some true` if positive. -/
def ratSign (r : RatConst) : Option Bool :=
  if r.isZero then none
  else some (r.num > 0)

/-- Leading coefficient and degree of a non-zero poly. -/
def polyLead (p : Poly) : Option (RatConst × Nat) :=
  let p := Poly.strip p
  if p.isZero then none
  else
    let d := p.deg
    if d < 0 then none
    else some (Poly.lc p, d.toNat)

/-- Limit of a polynomial as x → ±∞. -/
def limitPolyInf (p : Poly) (pos : Bool) : LimitResult :=
  let p := Poly.strip p
  if p.isZero then .value zero
  else if p.deg == 0 then .value (ofRat (Poly.coeff p 0))
  else
    match polyLead p with
    | none => .value zero
    | some (a, d) =>
      -- sign of x^d as x → ±∞
      let xPos := pos || (d % 2 == 0)
      match ratSign a with
      | none => .value zero
      | some aPos =>
        -- product positive ⇒ +∞ iff a and x^d have the same sign
        .infinity (aPos == xPos)

/-- Limit of rational p/q as x → ±∞. -/
def limitRatInf (num den : Poly) (pos : Bool) : LimitResult :=
  let num := Poly.strip num
  let den := Poly.strip den
  if den.isZero then .undetermined "division by zero polynomial"
  else if num.isZero then .value zero
  else
    match polyLead num, polyLead den with
    | some (an, dn), some (ad, dd) =>
      if dn > dd then
        match RatConst.div an ad with
        | none => .undetermined "leading coefficient division failed"
        | some ratio =>
          let degDiff := dn - dd
          let xSign := if pos then true else (degDiff % 2 == 0)
          match ratSign ratio with
          | none => .value zero
          | some rPos => .infinity (rPos == xSign)
      else if dn < dd then .value zero
      else
        match RatConst.div an ad with
        | some r => .value (ofRat r)
        | none => .undetermined "leading coefficient division failed"
    | _, _ => .undetermined "empty leading terms"

/-- Evaluate a poly at a rational point. -/
def evalPolyAt (p : Poly) (a : RatConst) : RatConst :=
  Poly.eval p a

/-- L'Hôpital / rational finite limits. -/
partial def limitRatFinite (num den : Poly) (a : RatConst) (fuel : Nat) : LimitResult :=
  match fuel with
  | 0 => .undetermined "L'Hôpital fuel exhausted"
  | fuel'+1 =>
    let n0 := evalPolyAt num a
    let d0 := evalPolyAt den a
    if d0.isZero then
      if n0.isZero then
        -- 0/0 → differentiate
        limitRatFinite (Poly.differentiate num) (Poly.differentiate den) a fuel'
      else
        -- c/0 → ±∞ (simple pole: use sign of n0/d'(a) from the right)
        let d1 := evalPolyAt (Poly.differentiate den) a
        if d1.isZero then
          .undetermined s!"pole of order > 1 or indeterminate at {a}"
        else
          match ratSign n0, ratSign d1 with
          | some nPos, some dPos =>
            .infinity (nPos == dPos)
          | _, _ => .undetermined "zero sign at pole"
    else
      match RatConst.div n0 d0 with
      | some r => .value (ofRat r)
      | none => .undetermined "division failed"

/-- Limit of a rational expression (via `RatFn`) at a point. -/
partial def limitRatFn (r : RatFn) (v : String) (pt : LimitPoint) (fuel : Nat) : LimitResult :=
  let r := RatFn.simplify r
  match pt with
  | .posInf => limitRatInf r.num r.den true
  | .negInf => limitRatInf r.num r.den false
  | .finite a =>
    match asRatConst a with
    | some q => limitRatFinite r.num r.den q fuel
    | none =>
      -- symbolic finite point: substitute and simplify
      let e := RatFn.toExpr r v
      let e' := simplify (subst e v a)
      match eval? e' with
      | some c => .value (const c)
      | none =>
        if dependsOn e' v then .undetermined s!"limit still depends on {v}"
        else .value e'

where
  asRatConst : Expr → Option RatConst
    | const c => CplxConst.toRat? c
    | _ => none

/--
  General limit: prefer rational analysis; else continuous substitution
  for finite points; basic ±∞ heuristics for polynomials / leading growth.
-/
partial def limit (e : Expr) (v : String) (pt : LimitPoint) (fuel : Nat := 16) : LimitResult :=
  let e := simplify e
  -- Independent of v
  if !dependsOn e v then
    match pt with
    | .finite _ | .posInf | .negInf => .value e
  else
    match RatFn.ofExpr? e v with
    | some r => limitRatFn r v pt fuel
    | none =>
      match pt with
      | .finite a =>
        let e' := simplify (subst e v a)
        match eval? e' with
        | some c => .value (const c)
        | none =>
          if dependsOn e' v then .undetermined s!"could not eliminate {v}"
          else
            -- may still have sin(0) etc. already simplified
            .value e'
      | .posInf | .negInf =>
        -- Try as poly
        match asPolyIn? e v with
        | some p =>
          let pos := match pt with | .posInf => true | _ => false
          limitPolyInf p pos
        | none =>
          -- peel c * f
          match e with
          | exp arg =>
            -- exp → +∞ if arg → +∞, → 0 if arg → −∞
            match limit arg v pt fuel with
            | .infinity pos => if pos then .infinity true else .value zero
            | .value c =>
              match eval? c with
              | some z =>
                match CplxConst.toRat? z with
                | some q =>
                  if q.isZero then .value one
                  else .value (exp c)  -- leave symbolic exp(const)
                | none => .value (exp c)
              | none => .value (exp c)
            | .undetermined msg => .undetermined msg
          | ln arg =>
            match limit arg v pt fuel with
            | .infinity true => .infinity true
            | .infinity false => .undetermined "ln of −∞"
            | .value c =>
              match eval? c with
              | some z =>
                match CplxConst.toRat? z with
                | some q =>
                  if q.isZero then .infinity false  -- ln 0+ → −∞
                  else if q.num > 0 then .value (ln c)
                  else .undetermined "ln of non-positive"
                | none => .value (ln c)
              | none => .value (ln c)
            | .undetermined msg => .undetermined msg
          | _ => .undetermined s!"no limit method for {e} at {pt}"

/-- Convenience: limit as expression (throws on undetermined via Option). -/
def limitExpr? (e : Expr) (v : String) (pt : LimitPoint) : Option Expr :=
  match limit e v pt with
  | .value r => some r
  | .infinity true => some (var "∞")
  | .infinity false => some (neg (var "∞"))
  | .undetermined _ => none

/-- `limit(e, v, a)` with `a` an expression (including `oo`). -/
def limitAt (e : Expr) (v : String) (a : Expr) : LimitResult :=
  limit e v (LimitPoint.ofExpr a)

end Taschenrechner
