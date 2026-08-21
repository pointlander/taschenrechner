/-
  Symbolic limits.

  * Two-sided and one-sided (left/right) limits
  * Finite points for rationals (L'Hôpital on 0/0; poles via zero orders)
  * ±∞ for rational functions via degree / leading coefficients
  * Pole order and singularity classification for rationals
  * Continuous elementary substitution when the limit is ground
  * Elementary 0/0 and poles via truncated series about the point
    (and `x → ±∞` via `t = 1/x`)
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Eval
import Taschenrechner.Normal
import Taschenrechner.Solve
import Taschenrechner.Series

namespace Taschenrechner

open Expr

/-! ### Sides and limit points -/

/-- Approach direction at a finite point. -/
inductive LimitSide where
  /-- Two-sided limit (default). -/
  | both
  /-- x → a⁻ (from the left). -/
  | left
  /-- x → a⁺ (from the right). -/
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

namespace LimitSide

def toString : LimitSide → String
  | .both => "two-sided"
  | .left => "left"
  | .right => "right"

instance : ToString LimitSide where
  toString := toString

/-- Parse direction from an expression: `1`/`right`/`+` → right; `-1`/`left` → left. -/
def ofExpr? (e : Expr) : Option LimitSide :=
  let e := Expr.simplify e
  match e with
  | const c =>
    match CplxConst.toRat? c with
    | some q =>
      if q.num > 0 then some .right
      else if q.num < 0 then some .left
      else none
    | none => none
  | var name =>
    let n := name.toLower
    if n == "right" || n == "r" || n == "plus" || n == "pos" then some .right
    else if n == "left" || n == "l" || n == "minus" || n == "neg" then some .left
    else if n == "both" || n == "two" then some .both
    else none
  | _ => none

end LimitSide

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
    match e with
    | mul (const c) rest =>
      match ofExpr rest with
      | .posInf => if c.isReal && c.re.num < 0 then .negInf else .posInf
      | .negInf => if c.isReal && c.re.num < 0 then .posInf else .negInf
      | .finite _ => .finite e
    | _ => .finite e

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
  /-- Could not decide (including jump discontinuities when two-sided). -/
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

def beq : LimitResult → LimitResult → Bool
  | .value a, .value b => a == b
  | .infinity p, .infinity q => p == q
  | .undetermined _, .undetermined _ => true
  | _, _ => false

instance : BEq LimitResult where beq := beq

end LimitResult

/-! ### Singularity classification -/

inductive Singularity where
  /-- Limit exists and is finite (function may still be undefined at the point). -/
  | removable : Expr → Singularity
  /-- Continuous / defined with that value (same as removable for our purposes). -/
  | continuous : Expr → Singularity
  /-- Pole of given order; one-sided limits to ±∞. -/
  | pole : (order : Nat) → (left : LimitResult) → (right : LimitResult) → Singularity
  /-- Finite left and right limits differ. -/
  | jump : LimitResult → LimitResult → Singularity
  | undetermined : String → Singularity
  deriving Repr, Inhabited

namespace Singularity

def toString : Singularity → String
  | .removable e => s!"removable singularity, limit = {e}"
  | .continuous e => s!"continuous, value = {e}"
  | .pole k L R => s!"pole of order {k}, lim- = {L}, lim+ = {R}"
  | .jump L R => s!"jump discontinuity, lim- = {L}, lim+ = {R}"
  | .undetermined msg => s!"undetermined ({msg})"

instance : ToString Singularity where
  toString := toString

/--
  Encode classification as an expression for the REPL:
  * continuous/removable → the finite value
  * pole → 1×3 matrix `[order, lim-, lim+]`
  * jump → 1×2 matrix `[lim-, lim+]`
  * undetermined → variable `undetermined`
-/
def toExpr : Singularity → Expr
  | .removable e | .continuous e => e
  | .pole k L R =>
    Expr.mat #[#[Expr.ofNat k, L.toExpr, R.toExpr]]
  | .jump L R =>
    Expr.mat #[#[L.toExpr, R.toExpr]]
  | .undetermined _ => var "undetermined"

def toExpr? : Singularity → Except String Expr
  | .undetermined msg => throw msg
  | s => pure s.toExpr

end Singularity

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

/-- Multiplicity of the root `a` of `p` (0 if `p(a) ≠ 0`). -/
partial def zeroOrder (p : Poly) (a : RatConst) (fuel : Nat := 64) : Nat :=
  let p := Poly.strip p
  if p.isZero then fuel  -- treat as infinite; capped
  else
    match fuel with
    | 0 => 0
    | fuel'+1 =>
      if !(Poly.eval p a).isZero then 0
      else 1 + zeroOrder (Poly.differentiate p) a fuel'

/-- Limit of a polynomial as x → ±∞. -/
def limitPolyInf (p : Poly) (pos : Bool) : LimitResult :=
  let p := Poly.strip p
  if p.isZero then .value zero
  else if p.deg == 0 then .value (ofRat (Poly.coeff p 0))
  else
    match polyLead p with
    | none => .value zero
    | some (a, d) =>
      let xPos := pos || (d % 2 == 0)
      match ratSign a with
      | none => .value zero
      | some aPos => .infinity (aPos == xPos)

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

/--
  One-sided (or two-sided) rational limit at a finite rational point
  using zero orders: cancel (x−a) factors, then finite value or ±∞ pole.
-/
partial def limitRatFinite (num den : Poly) (a : RatConst) (side : LimitSide) (fuel : Nat) :
    LimitResult :=
  match fuel with
  | 0 => .undetermined "limit fuel exhausted"
  | fuel'+1 =>
    let num := Poly.strip num
    let den := Poly.strip den
    if den.isZero then .undetermined "division by zero polynomial"
    else
      let nOrd := zeroOrder num a
      let dOrd := zeroOrder den a
      if dOrd == 0 then
        -- den(a) ≠ 0
        let n0 := evalPolyAt num a
        let d0 := evalPolyAt den a
        match RatConst.div n0 d0 with
        | some r => .value (ofRat r)
        | none => .undetermined "division failed"
      else if nOrd >= dOrd then
        -- removable / finite after cancel: use L'Hôpital nOrd times or divide by (x-a)
        if nOrd > 0 && dOrd > 0 then
          -- cancel one (x-a) via differentiation ratio for 0/0
          limitRatFinite (Poly.differentiate num) (Poly.differentiate den) a side fuel'
        else
          let n0 := evalPolyAt num a
          let d0 := evalPolyAt den a
          if d0.isZero then
            limitRatFinite (Poly.differentiate num) (Poly.differentiate den) a side fuel'
          else
            match RatConst.div n0 d0 with
            | some r => .value (ofRat r)
            | none => .undetermined "division failed"
      else
        -- Pole of order k = dOrd - nOrd
        let k := dOrd - nOrd
        -- Leading coefficient of cancelled form: num^{(n)}(a)/n!  over  den^{(d)}(a)/d!
        -- Sign of C in C/(x-a)^k from high derivatives:
        let nDeriv :=
          Id.run do
            let mut p := num
            for _ in [:nOrd] do p := Poly.differentiate p
            pure p
        let dDeriv :=
          Id.run do
            let mut p := den
            for _ in [:dOrd] do p := Poly.differentiate p
            pure p
        let nLead := evalPolyAt nDeriv a
        let dLead := evalPolyAt dDeriv a
        if dLead.isZero then
          .undetermined "pole analysis failed (vanishing derivative)"
        else
          match RatConst.div nLead dLead with
          | none => .undetermined "pole coefficient division failed"
          | some c =>
            -- factorial ratio is positive, so sign(C) = sign(c)
            match ratSign c with
            | none => .undetermined "zero residue at pole"
            | some cPos =>
              -- f ~ C' / (x-a)^k with sign(C') = cPos
              -- x→a+: (x-a)^k > 0 → sign f = cPos
              -- x→a-: (x-a)^k has sign (-1)^k → sign f = cPos XOR (k odd)
              let rightPos := cPos
              let leftPos := if k % 2 == 0 then cPos else !cPos
              match side with
              | .right => .infinity rightPos
              | .left => .infinity leftPos
              | .both =>
                if rightPos == leftPos then .infinity rightPos
                else
                  let ls := if leftPos then "+∞" else "-∞"
                  let rs := if rightPos then "+∞" else "-∞"
                  .undetermined s!"two-sided limit does not exist (left {ls}, right {rs})"

/-! ### Series-based limits -/

/-- Sign of a ground real expression: `some true` if positive. -/
def exprSignPos? (e : Expr) : Option Bool :=
  match eval? (simplify e) with
  | some c =>
    match CplxConst.toRat? c with
    | some q => if q.isZero then none else some (q.num > 0)
    | none => none
  | none => none

/-- Dummy variable for the substitution `x = ±1/t` at infinity. -/
def seriesInfVar : String := "__t"

/--
  Read a two-sided or one-sided limit from a Laurent series in the local
  coordinate `u → 0`.
-/
def limitFromSeries (s : TruncSeries) (side : LimitSide) : LimitResult :=
  let s := TruncSeries.strip s
  if s.coeffs.isEmpty then .value zero
  else if s.offset > 0 then .value zero
  else if s.offset == 0 then
    .value (simplify s.coeffs[0]!)
  else
    let k := s.offset.natAbs
    let c := simplify s.coeffs[0]!
    match exprSignPos? c with
    | none =>
      -- Even-order pole of unknown sign: still ±∞ both sides if we can
      -- only say it diverges; leave undetermined.
      .undetermined s!"series pole of order {k} (unknown leading sign)"
    | some cPos =>
      let rightPos := cPos
      let leftPos := if k % 2 == 0 then cPos else !cPos
      match side with
      | .right => .infinity rightPos
      | .left => .infinity leftPos
      | .both =>
        if rightPos == leftPos then .infinity rightPos
        else
          .undetermined s!"two-sided limit does not exist (series pole order {k})"

/-- Series expansion of `e` about a finite point or at ±∞. -/
def limitBySeries (e : Expr) (v : String) (pt : LimitPoint) (side : LimitSide) :
    Option LimitResult :=
  match pt with
  | .finite a =>
    match seriesAbout e v a seriesMaxDeg with
    | some s => some (limitFromSeries s side)
    | none => none
  | .posInf =>
    let t := seriesInfVar
    let e' := subst e v (div one (var t))
    match seriesAbout e' t zero seriesMaxDeg with
    | some s => some (limitFromSeries s .right)
    | none => none
  | .negInf =>
    let t := seriesInfVar
    let e' := subst e v (neg (div one (var t)))
    match seriesAbout e' t zero seriesMaxDeg with
    | some s => some (limitFromSeries s .right)
    | none => none

/-- Limit of a rational expression (via `RatFn`) at a point. -/
partial def limitRatFn (r : RatFn) (v : String) (pt : LimitPoint) (side : LimitSide)
    (fuel : Nat) : LimitResult :=
  let r := RatFn.simplify r
  match pt with
  | .posInf => limitRatInf r.num r.den true
  | .negInf => limitRatInf r.num r.den false
  | .finite a =>
    match asRatConst a with
    | some q => limitRatFinite r.num r.den q side fuel
    | none =>
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
  General limit with optional one-sided approach at finite points.
  At ±∞ the side is ignored.
-/
partial def limit (e : Expr) (v : String) (pt : LimitPoint) (side : LimitSide := .both)
    (fuel : Nat := 16) : LimitResult :=
  let e := simplify e
  if !dependsOn e v then
    .value e
  else
    match RatFn.ofExpr? e v with
    | some r => limitRatFn r v pt side fuel
    | none =>
      match limitBySeries e v pt side with
      | some r => r
      | none =>
      match pt with
      | .finite a =>
        let e' := simplify (subst e v a)
        match eval? e' with
        | some c => .value (const c)
        | none =>
          if dependsOn e' v then .undetermined s!"could not eliminate {v}"
          else .value e'
      | .posInf | .negInf =>
        match asPolyIn? e v with
        | some p =>
          let pos := match pt with | .posInf => true | _ => false
          limitPolyInf p pos
        | none =>
          match e with
          | exp arg =>
            match limit arg v pt side fuel with
            | .infinity pos => if pos then .infinity true else .value zero
            | .value c =>
              match eval? c with
              | some z =>
                match CplxConst.toRat? z with
                | some q =>
                  if q.isZero then .value one
                  else .value (exp c)
                | none => .value (exp c)
              | none => .value (exp c)
            | .undetermined msg => .undetermined msg
          | ln arg =>
            match limit arg v pt side fuel with
            | .infinity true => .infinity true
            | .infinity false => .undetermined "ln of −∞"
            | .value c =>
              match eval? c with
              | some z =>
                match CplxConst.toRat? z with
                | some q =>
                  if q.isZero then
                    -- ln(0+)=−∞; ln(0−) undefined
                    match side with
                    | .left => .undetermined "ln of 0 from the left"
                    | .right | .both => .infinity false
                  else if q.num > 0 then .value (ln c)
                  else .undetermined "ln of non-positive"
                | none => .value (ln c)
              | none => .value (ln c)
            | .undetermined msg => .undetermined msg
          | _ => .undetermined s!"no limit method for {e} at {pt}"

/-- Convenience: limit as expression. -/
def limitExpr? (e : Expr) (v : String) (pt : LimitPoint) (side : LimitSide := .both) :
    Option Expr :=
  match limit e v pt side with
  | .value r => some r
  | .infinity true => some (var "∞")
  | .infinity false => some (neg (var "∞"))
  | .undetermined _ => none

/-- `limit(e, v, a)` with `a` an expression (including `oo`). -/
def limitAt (e : Expr) (v : String) (a : Expr) (side : LimitSide := .both) : LimitResult :=
  limit e v (LimitPoint.ofExpr a) side

/-- One-sided helpers. -/
def limitLeft (e : Expr) (v : String) (a : Expr) : LimitResult :=
  limitAt e v a .left

def limitRight (e : Expr) (v : String) (a : Expr) : LimitResult :=
  limitAt e v a .right

/-! ### Pole order & classification -/

/--
  Order of a pole of a rational `e` at rational `a` (in free var `v`).
  Returns `none` if not a pole (including removable / continuous / non-rational).
  Order 0 is not used; removable singularities yield `none`.
-/
def poleOrder? (e : Expr) (v : String) (a : Expr) : Option Nat :=
  match RatFn.ofExpr? (simplify e) v, asRat a with
  | some r, some q =>
    let r := RatFn.simplify r
    let nOrd := zeroOrder r.num q
    let dOrd := zeroOrder r.den q
    if dOrd > nOrd then some (dOrd - nOrd) else none
  | _, _ => none
where
  asRat : Expr → Option RatConst
    | const c => CplxConst.toRat? c
    | _ => none

/-- Pole order as expression (0 if not a pole). -/
def poleOrderExpr (e : Expr) (v : String) (a : Expr) : Expr :=
  match poleOrder? e v a with
  | some k => ofNat k
  | none => zero

/-- Classify the singularity of `e` at finite point `a`. -/
def classifyAt (e : Expr) (v : String) (a : Expr) : Singularity :=
  let e := simplify e
  match LimitPoint.ofExpr a with
  | .posInf | .negInf =>
    .undetermined "classify is for finite points (use limit at oo)"
  | .finite a0 =>
    match RatFn.ofExpr? e v, asRat a0 with
    | some r, some q =>
      let r := RatFn.simplify r
      let nOrd := zeroOrder r.num q
      let dOrd := zeroOrder r.den q
      let L := limitRatFinite r.num r.den q .left 16
      let R := limitRatFinite r.num r.den q .right 16
      if dOrd == 0 then
        -- defined / continuous at a
        match L with
        | .value c => .continuous c
        | _ => .undetermined "unexpected non-finite limit at regular point"
      else if nOrd >= dOrd then
        -- removable
        match limitRatFinite r.num r.den q .both 16 with
        | .value c => .removable c
        | r => .undetermined s!"removable analysis: {r}"
      else
        let k := dOrd - nOrd
        .pole k L R
    | none, _ =>
      -- non-rational: try two-sided + one-sided limits
      let L := limit e v (.finite a0) .left
      let R := limit e v (.finite a0) .right
      let B := limit e v (.finite a0) .both
      match B with
      | .value c => .removable c
      | .infinity pos => .pole 1 (.infinity pos) (.infinity pos)
      | .undetermined _ =>
        match L, R with
        | .value lv, .value rv =>
          if lv == rv then .removable lv else .jump L R
        | .infinity lp, .infinity rp =>
          if lp == rp then .pole 1 L R else .jump L R
        | .value _, .infinity _ | .infinity _, .value _ => .jump L R
        | _, _ => .undetermined s!"could not classify at {a0}"
    | some _, none =>
      .undetermined s!"classify needs a rational point, got {a0}"
where
  asRat : Expr → Option RatConst
    | const c => CplxConst.toRat? c
    | _ => none

end Taschenrechner
