/-
  Ordinary differential equations.

  * First-order linear:  y' + P(x) y = Q(x)   → integrating factor
  * Bernoulli: y' + P(x) y = Q(x) y^n        → v = y^{1−n} reduces to linear
  * Separable: y' = f(x) g(y)     → ∫ dy/g = ∫ f dx
  * Second-order constant-coeff: a y'' + b y' + c y = g(x)
    (undetermined coefficients for sin/cos; else variation of parameters)
  * Linear systems: Y' = A Y  → Y = expm(A x) · C  (via Jordan form)
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Integrate
import Taschenrechner.Normal
import Taschenrechner.Eval
import Taschenrechner.Solve
import Taschenrechner.Matrix
import Taschenrechner.Eigen

namespace Taschenrechner

open Expr
open Taschenrechner.Expr (flattenMul)

/-- Arbitrary constant of integration in ODE solutions. -/
def odeC : Expr := var "C"

/-- Named free constants C1, C2, … (1-based). -/
def odeCi (i : Nat) : Expr :=
  var s!"C{i + 1}"

/--
  Represent y' as the free variable `yp` (or `y'` / `dy`) by convention, and y as `y`.

  * Dependent unknown is `y` (function of `x`)
  * First derivative: `yp` / `y'` / `dy`
  * Second derivative: `ypp` / `y''` / `d2y`
  * Example: `dsolve(yp + P*y = Q, y, x)`, `dsolve(y'' + y = 0)`
-/
def ypName : String := "yp"
def yppName : String := "ypp"

private def isYpName (name : String) : Bool :=
  name == ypName || name == "y'" || name == "dy"

private def isYppName (name : String) : Bool :=
  name == yppName || name == "y''" || name == "d2y"

private def dependsOnYFamily (e : Expr) (y : String) : Bool :=
  dependsOn e y || dependsOn e ypName || dependsOn e "y'" || dependsOn e "dy"
    || dependsOn e yppName || dependsOn e "y''" || dependsOn e "d2y"

/-- Collect coefficient of `yp` and of `y` in a linear expression in those symbols. -/
partial def linearFormInY (e : Expr) (y : String) (_x : String) : Option (Expr × Expr × Expr) :=
  -- Returns (A, B, C) for A*yp + B*y + C = 0 with A,B,C independent of y, yp
  -- Fails (none) if a second derivative appears.
  let e := simplify e
  go e
where
  go : Expr → Option (Expr × Expr × Expr)
  | add a b =>
    match go a, go b with
    | some (a1, b1, c1), some (a2, b2, c2) =>
      some (simplify (add a1 a2), simplify (add b1 b2), simplify (add c1 c2))
    | _, _ => none
  | mul (const c) rest =>
    match go rest with
    | some (a, b, c0) =>
      some (simplify (mul (const c) a), simplify (mul (const c) b), simplify (mul (const c) c0))
    | none => none
  | mul rest (const c) => go (mul (const c) rest)
  | var name =>
    if isYppName name then none
    else if isYpName name then
      some (one, zero, zero)
    else if name == y then
      some (zero, one, zero)
    else
      some (zero, zero, var name)
  | const c => some (zero, zero, const c)
  | e =>
    if dependsOnYFamily e y then
      match e with
      | mul a b =>
        let aY := dependsOnYFamily a y
        let bY := dependsOnYFamily b y
        if aY && !bY then
          match go a with
          | some (aa, bb, cc) =>
            if cc == zero then
              some (simplify (mul aa b), simplify (mul bb b), zero)
            else none
          | none => none
        else if bY && !aY then
          match go b with
          | some (aa, bb, cc) =>
            if cc == zero then
              some (simplify (mul aa a), simplify (mul bb a), zero)
            else none
          | none => none
        else none
      | _ => none
    else
      some (zero, zero, e)

/--
  Linear form in y'', y', y:
  returns `(A, B, C, D)` for `A·y'' + B·y' + C·y + D = 0`.
-/
partial def linearFormInY2 (e : Expr) (y : String) : Option (Expr × Expr × Expr × Expr) :=
  let e := simplify e
  go e
where
  go : Expr → Option (Expr × Expr × Expr × Expr)
  | add a b =>
    match go a, go b with
    | some (a1, b1, c1, d1), some (a2, b2, c2, d2) =>
      some (
        simplify (add a1 a2), simplify (add b1 b2),
        simplify (add c1 c2), simplify (add d1 d2))
    | _, _ => none
  | mul (const c) rest =>
    match go rest with
    | some (a, b, c0, d0) =>
      some (
        simplify (mul (const c) a), simplify (mul (const c) b),
        simplify (mul (const c) c0), simplify (mul (const c) d0))
    | none => none
  | mul rest (const c) => go (mul (const c) rest)
  | var name =>
    if isYppName name then some (one, zero, zero, zero)
    else if isYpName name then some (zero, one, zero, zero)
    else if name == y then some (zero, zero, one, zero)
    else some (zero, zero, zero, var name)
  | const c => some (zero, zero, zero, const c)
  | e =>
    if dependsOnYFamily e y then
      match e with
      | mul a b =>
        let aY := dependsOnYFamily a y
        let bY := dependsOnYFamily b y
        if aY && !bY then
          match go a with
          | some (aa, bb, cc, dd) =>
            if dd == zero then
              some (
                simplify (mul aa b), simplify (mul bb b),
                simplify (mul cc b), zero)
            else none
          | none => none
        else if bY && !aY then
          match go b with
          | some (aa, bb, cc, dd) =>
            if dd == zero then
              some (
                simplify (mul aa a), simplify (mul bb a),
                simplify (mul cc a), zero)
            else none
          | none => none
        else none
      | _ => none
    else
      some (zero, zero, zero, e)

/-- Rewrite equation to residual A*yp + B*y + C (= 0). -/
def odeResidual (e : Expr) (y x : String) : Option (Expr × Expr × Expr) :=
  let e := equationToZero (simplify e)
  linearFormInY e y x

/-- Residual A y'' + B y' + C y + D = 0. -/
def odeResidual2 (e : Expr) (y : String) : Option (Expr × Expr × Expr × Expr) :=
  let e := equationToZero (simplify e)
  linearFormInY2 e y

/-- Expression is a rational constant (no free symbols of interest). -/
def asRatConstExpr? (e : Expr) : Option RatConst :=
  match simplify e with
  | const c => CplxConst.toRat? c
  | _ => none

/-- True if `e` does not depend on any of the listed names. -/
def indepOf (e : Expr) (names : List String) : Bool :=
  names.all (fun v => !dependsOn e v)

/-! ### Exponential tidy (C/exp(f) → C·exp(−f), etc.) -/

/-- Rewrite expressions into a nicer exp form for ODE solutions. -/
partial def tidyExpForm : Expr → Expr
  | add a b => simplify (add (tidyExpForm a) (tidyExpForm b))
  | mul a b =>
    let a := tidyExpForm a
    let b := tidyExpForm b
    match a, b with
    -- exp(u)·exp(v) → exp(u+v)
    | exp u, exp v => simplify (exp (add u v))
    -- exp(u) · (exp(v)·p + q) → exp(u+v)·p + exp(u)·q
    | exp u, add (mul (exp v) p) q =>
      simplify (add (mul (exp (add u v)) p) (mul (exp u) q))
    | exp u, add q (mul (exp v) p) =>
      simplify (add (mul (exp u) q) (mul (exp (add u v)) p))
    | add (mul (exp v) p) q, exp u =>
      tidyExpForm (mul (exp u) (add (mul (exp v) p) q))
    | add q (mul (exp v) p), exp u =>
      tidyExpForm (mul (exp u) (add q (mul (exp v) p)))
    | _, _ =>
      match b with
      | pow (exp u) (const r) =>
        match CplxConst.toRat? r with
        | some q =>
          if q == RatConst.negOne then
            simplify (mul a (exp (neg u)))
          else if q.den == 1 then
            simplify (mul a (exp (mul (ofRat q) u)))
          else simplify (mul a b)
        | none => simplify (mul a b)
      | exp u =>
        match a with
        | pow (exp v) (const r) =>
          match CplxConst.toRat? r with
          | some q =>
            if q == RatConst.negOne then simplify (exp (sub u v))
            else simplify (mul a b)
          | none => simplify (mul a b)
        | _ => simplify (mul a b)
      | _ => simplify (mul a b)
  | pow (exp u) e =>
    let e := tidyExpForm e
    match e with
    | const r =>
      match CplxConst.toRat? r with
      | some q =>
        if q == RatConst.negOne then exp (neg (tidyExpForm u))
        else if q.isOne then exp (tidyExpForm u)
        else if q.den == 1 then exp (mul (ofRat q) (tidyExpForm u))
        else pow (exp (tidyExpForm u)) e
      | none => pow (exp (tidyExpForm u)) e
    | _ => pow (exp (tidyExpForm u)) e
  | pow a b => pow (tidyExpForm a) (tidyExpForm b)
  | exp e => exp (tidyExpForm e)
  | eq a b => eq (tidyExpForm a) (tidyExpForm b)
  | lt a b => lt (tidyExpForm a) (tidyExpForm b)
  | le a b => le (tidyExpForm a) (tidyExpForm b)
  | sin e => sin (tidyExpForm e)
  | cos e => cos (tidyExpForm e)
  | tan e => tan (tidyExpForm e)
  | sinh e => sinh (tidyExpForm e)
  | cosh e => cosh (tidyExpForm e)
  | tanh e => tanh (tidyExpForm e)
  | ln e => ln (tidyExpForm e)
  | atan e => atan (tidyExpForm e)
  | asin e => asin (tidyExpForm e)
  | acos e => acos (tidyExpForm e)
  | sec e => sec (tidyExpForm e)
  | csc e => csc (tidyExpForm e)
  | cot e => cot (tidyExpForm e)
  | factorial e => factorial (tidyExpForm e)
  | gamma e => gamma (tidyExpForm e)
  | floor e => floor (tidyExpForm e)
  | Expr.ite c t e => Expr.ite (tidyExpForm c) (tidyExpForm t) (tidyExpForm e)
  | abs e => abs (tidyExpForm e)
  | re e => re (tidyExpForm e)
  | im e => im (tidyExpForm e)
  | conj e => conj (tidyExpForm e)
  | e => e

/--
  Pull division by exp through sums:
  (exp(u)·a + b) · exp(u)^(-1) → a + b·exp(−u)
-/
partial def expandDivExp (e : Expr) : Expr :=
  let e := simplify e
  match e with
  | mul (add a b) (pow (exp u) (const r)) =>
    match CplxConst.toRat? r with
    | some q =>
      if q == RatConst.negOne then
        let a' := tidyExpForm (simplify (mul a (pow (exp u) (const r))))
        let b' := tidyExpForm (simplify (mul b (pow (exp u) (const r))))
        simplify (add a' b')
      else e
    | none => e
  | mul (pow (exp u) (const r)) (add a b) =>
    expandDivExp (mul (add a b) (pow (exp u) (const r)))
  | add a b => simplify (add (expandDivExp a) (expandDivExp b))
  | mul a b =>
    let t := tidyExpForm (mul a b)
    if t == e then e else expandDivExp t
  | eq a b => eq (expandDivExp a) (expandDivExp b)
  | lt a b => lt (expandDivExp a) (expandDivExp b)
  | le a b => le (expandDivExp a) (expandDivExp b)
  | e => tidyExpForm e

def tidyODESol (e : Expr) : Expr :=
  simplify (expandDivExp (tidyExpForm e))

/--
  Solve linear first-order ODE: A(x) y' + B(x) y + C(x) = 0
  i.e. y' + P y = Q with P = B/A, Q = −C/A (A ≠ 0).
-/
def dsolveLinear (A B C : Expr) (y x : String) : Except String Expr :=
  let A := simplify A
  let B := simplify B
  let C := simplify C
  if isZeroExpr A x then
    throw "dsolve: coefficient of y' is zero (not first-order in yp)"
  else
    let P := simplify (div B A)
    let Q := simplify (neg (div C A))
    -- μ = exp(∫ P dx)
    match integrate P x with
    | .success iP _ =>
      let mu := simplify (exp iP)
      -- ∫ μ Q dx
      let muQ := simplify (mul mu Q)
      match integrate muQ x with
      | .success iMuQ _ =>
        -- y = (1/μ) * (iMuQ + C)
        let num := simplify (add iMuQ odeC)
        let sol := tidyODESol (eq (var y) (div num mu))
        pure sol
      | .notElementary r => throw s!"dsolve: ∫ μ·Q not elementary: {r}"
      | .failure r => throw s!"dsolve: ∫ μ·Q failed: {r}"
    | .notElementary r => throw s!"dsolve: ∫ P not elementary: {r}"
    | .failure r => throw s!"dsolve: ∫ P failed: {r}"

/-- If left side is ln(y) or c·ln(y), invert to y = … -/
def explicitFromImplicit (left right : Expr) (y : String) : Expr :=
  let left := simplify left
  let right := simplify right
  match left with
  | ln (var name) =>
    if name == y then tidyODESol (eq (var y) (exp right))
    else eq left right
  | mul (const c) (ln (var name)) =>
    if name == y then
      -- c ln y = right → ln y = right/c → y = exp(right/c)
      match CplxConst.toRat? c with
      | some q =>
        if q.isZero then eq left right
        else
          match RatConst.inv q with
          | some inv => tidyODESol (eq (var y) (exp (mul (ofRat inv) right)))
          | none => eq left right
      | none => eq left right
    else eq left right
  | _ => eq left right

/-- Split product into factor depending only on x and only on y. -/
def splitSeparable (e : Expr) (x y : String) : Option (Expr × Expr) :=
  let e := simplify e
  if !dependsOn e y && dependsOn e x then some (e, one)
  else if dependsOn e y && !dependsOn e x then some (one, e)
  else if !dependsOn e y && !dependsOn e x then some (e, one)
  else
    let fs := flattenMul e
    let (fx, fy, mixed) :=
      fs.foldl (fun (ax, ay, m) t =>
        let dx := dependsOn t x
        let dy := dependsOn t y
        if dy && !dx then (ax, ay ++ [t], m)
        else if dx && !dy then (ax ++ [t], ay, m)
        else if !dx && !dy then (ax ++ [t], ay, m)  -- constants → f
        else (ax, ay, true)) ([], [], false)
    if mixed then none
    else
      let f := if fx.isEmpty then one else fx.foldl (fun a b => mul a b) one
      let g := if fy.isEmpty then one else fy.foldl (fun a b => mul a b) one
      some (simplify f, simplify g)

/--
  Separable: A(x) y' = f(x) * g(y) written as yp = f(x)*g(y),
  residual: yp − f*g = 0 → A=1, and B,C not linear.
-/
def dsolveSeparable (A B C : Expr) (y x : String) : Except String Expr :=
  -- Require B = 0 (no naked y term) and A ≠ 0: yp = −C/A = f(x) g(y)
  if !isZeroExpr B x && dependsOn B y then
    throw "dsolve: not separable (linear y term present); try linear solver"
  else if isZeroExpr A x then
    throw "dsolve: missing y'"
  else
    let rhs := simplify (neg (div C A))  -- y' = rhs
    match splitSeparable rhs x y with
    | none => throw "dsolve: could not separate variables"
    | some (f, g) =>
      if isZeroExpr g y then throw "dsolve: g(y) = 0"
      else
        let invG := simplify (div one g)
        match integrate invG y with
        | .success Gy _ =>
          match integrate f x with
          | .success Fx _ =>
            pure (tidyODESol (explicitFromImplicit Gy (add Fx odeC) y))
          | .notElementary r => throw s!"dsolve: ∫ f(x) not elementary: {r}"
          | .failure r => throw s!"dsolve: ∫ f(x) failed: {r}"
        | .notElementary r => throw s!"dsolve: ∫ dy/g not elementary: {r}"
        | .failure r => throw s!"dsolve: ∫ dy/g failed: {r}"

/-! ### Bernoulli: y' + P(x) y = Q(x) y^n -/

def mergeYPowers (a b : List (RatConst × Expr)) : List (RatConst × Expr) :=
  let rec insert (ex : RatConst) (c : Expr) : List (RatConst × Expr) → List (RatConst × Expr)
    | [] =>
      let c := simplify c
      if c == zero || isZeroExpr c "x" then [] else [(ex, c)]
    | (ex', c') :: rest =>
      if ex == ex' then
        let s := simplify (add c c')
        if s == zero || isZeroExpr s "x" then rest else (ex, s) :: rest
      else (ex', c') :: insert ex c rest
  b.foldl (fun acc (ex, c) => insert ex c acc) a

def scaleYPowers (k : Expr) : List (RatConst × Expr) → List (RatConst × Expr)
  | [] => []
  | (ex, c) :: rest =>
    let s := simplify (mul k c)
    if s == zero || isZeroExpr s "x" then scaleYPowers k rest
    else (ex, s) :: scaleYPowers k rest

/-- Product of two y-power sums: only if one factor is free of `y`, or both monomials. -/
def mulYPowers (pa pb : List (RatConst × Expr)) : Option (List (RatConst × Expr)) :=
  let free (ps : List (RatConst × Expr)) : Option Expr :=
    match ps with
    | [] => some zero
    | [(ex, c)] => if ex.isZero then some c else none
    | _ =>
      if ps.all (fun (ex, _) => ex.isZero) then
        some (ps.foldl (fun acc (_, c) => add acc c) zero)
      else none
  match free pa, free pb with
  | some ca, some cb => some [(RatConst.zero, simplify (mul ca cb))]
  | some ca, none => some (scaleYPowers ca pb)
  | none, some cb => some (scaleYPowers cb pa)
  | none, none =>
    match pa, pb with
    | [(ea, ca)], [(eb, cb)] =>
      some [(ea + eb, simplify (mul ca cb))]
    | _, _ => none

/--
  Split a first-order residual into `A(x)·y' + Σ cᵢ(x) y^{eᵢ}`.
  Fails if `y'` is nonlinear or mixed with `y`.
-/
partial def collectFirstOrder (e : Expr) (y : String) :
    Option (Expr × List (RatConst × Expr)) :=
  go (simplify e)
where
  go : Expr → Option (Expr × List (RatConst × Expr))
  | add a b =>
    match go a, go b with
    | some (ya, pa), some (yb, pb) =>
      some (simplify (add ya yb), mergeYPowers pa pb)
    | _, _ => none
  | mul (const c) rest =>
    match go rest with
    | some (yp, ps) => some (simplify (mul (const c) yp), scaleYPowers (const c) ps)
    | none => none
  | mul rest (const c) => go (mul (const c) rest)
  | var name =>
    if isYppName name then none
    else if isYpName name then some (one, [])
    else if name == y then some (zero, [(RatConst.one, one)])
    else some (zero, [(RatConst.zero, var name)])
  | const c =>
    if c.isZero then some (zero, []) else some (zero, [(RatConst.zero, const c)])
  | pow base (const r) =>
    match CplxConst.toRat? r with
    | none => none
    | some q =>
      match go base with
      | none => none
      | some (yp, ps) =>
        if !(yp == zero || isZeroExpr yp "x") then none
        else
          match ps with
          | [] => some (zero, [(RatConst.zero, pow base (const r))])
          | [(ex, c)] =>
            some (zero, [(ex * q, simplify (pow c (const r)))])
          | _ => none
  | e =>
    if dependsOnYFamily e y then
      match e with
      | mul a b =>
        match go a, go b with
        | some (ya, pa), some (yb, pb) =>
          let ya0 := ya == zero || isZeroExpr ya "x"
          let yb0 := yb == zero || isZeroExpr yb "x"
          if !ya0 && !yb0 then none
          else if !ya0 then
            -- y' * (y-free)
            match pb with
            | [] => some (simplify (mul ya yb), [])
            | [(ex, c)] =>
              if ex.isZero then some (simplify (mul ya c), []) else none
            | _ => none
          else if !yb0 then
            match pa with
            | [] => some (simplify (mul yb ya), [])
            | [(ex, c)] =>
              if ex.isZero then some (simplify (mul yb c), []) else none
            | _ => none
          else
            match mulYPowers pa pb with
            | some ps => some (zero, ps)
            | none => none
        | _, _ => none
      | _ => none
    else
      some (zero, [(RatConst.zero, e)])

/-- `y' + P y = Q y^n` with `n ≠ 0,1` and `P,Q` free of `y`. -/
def bernoulliPQ? (e : Expr) (y x : String) : Option (Expr × Expr × RatConst) :=
  match collectFirstOrder (equationToZero (simplify e)) y with
  | none => none
  | some (ypC, powers) =>
    if ypC == zero || isZeroExpr ypC x then none
    else if dependsOnYFamily ypC y then none
    else
      let powers :=
        powers.filter fun (_, c) => !(c == zero || isZeroExpr c x)
      if powers.any fun (_, c) => dependsOnYFamily c y then none
      else if powers.any fun (ex, _) => ex.isZero then none
      else
        let lin := powers.find? fun (ex, _) => ex.isOne
        let others := powers.filter fun (ex, _) => !ex.isOne
        match others with
        | [(n, Dn)] =>
          if n.isOne || n.isZero then none
          else
            let B :=
              match lin with
              | some (_, b) => b
              | none => zero
            let P := simplify (div B ypC)
            let Q := simplify (neg (div Dn ypC))
            if dependsOn P y || dependsOn Q y then none
            else some (P, Q, n)
        | _ => none

/-- Invert `v = y^{1−n}` to an explicit `y = …`. -/
def yFromBernoulliV (vExpr : Expr) (n : RatConst) : Expr :=
  let k := RatConst.one - n
  if k == RatConst.negOne then simplify (div one vExpr)
  else if k.isOne then simplify vExpr
  else
    match RatConst.inv k with
    | none => pow vExpr (ofRat k)
    | some invk => simplify (pow vExpr (ofRat invk))

/--
  Bernoulli `y' + P(x) y = Q(x) y^n` (`n ≠ 1`):
  `v = y^{1−n}` satisfies `v' + (1−n) P v = (1−n) Q`.
-/
def dsolveBernoulli (e : Expr) (y x : String) : Except String Expr :=
  match bernoulliPQ? e y x with
  | none => throw "dsolve: not a Bernoulli equation y'+P y=Q y^n"
  | some (P, Q, n) =>
    let k := RatConst.one - n
    if k.isZero then throw "dsolve: Bernoulli n=1 is linear"
    else
      let kE := ofRat k
      let A := one
      let B := simplify (mul kE P)
      let C := simplify (neg (mul kE Q))
      match dsolveLinear A B C "__bernv" x with
      | .error msg => throw s!"dsolve Bernoulli: {msg}"
      | .ok sol =>
        match asEquation? sol with
        | some (lhs, rhs) =>
          if lhs == var "__bernv" then
            pure (tidyODESol (eq (var y) (yFromBernoulliV rhs n)))
          else throw "dsolve Bernoulli: expected v = …"
        | none => throw "dsolve Bernoulli: expected v = …"

/-- First-order: linear, then separable, then Bernoulli. -/
def dsolveFirstOrder (e : Expr) (y x : String) : Except String Expr :=
  match odeResidual e y x with
  | some (A, B, C) =>
    if !dependsOn B y && !dependsOn A y && !dependsOn C y then
      match dsolveLinear A B C y x with
      | .ok sol => pure (tidyODESol sol)
      | .error e1 =>
        match dsolveSeparable A B C y x with
        | .ok sol => pure (tidyODESol sol)
        | .error _ =>
          match dsolveBernoulli e y x with
          | .ok sol => pure sol
          | .error _ => throw e1
    else
      match dsolveSeparable A B C y x with
      | .ok sol => pure (tidyODESol sol)
      | .error e2 =>
        match dsolveBernoulli e y x with
        | .ok sol => pure sol
        | .error _ => throw e2
  | none =>
    match dsolveBernoulli e y x with
    | .ok sol => pure sol
    | .error eB =>
      throw s!"dsolve: expected ODE in y'/y or y''/y'/y (use y', yp, y'', ypp) or a square matrix A for Y'=A Y; {eB}"

/--
  Apply initial condition y(x0)=y0 to an explicit solution `y = f(x,C)`.
-/
def applyIC (sol : Expr) (y x : String) (x0 y0 : Expr) : Except String Expr :=
  match asEquation? sol with
  | none => throw "dsolve IC: expected explicit solution y = …"
  | some (lhs, rhs) =>
    if lhs != var y then
      -- implicit: substitute and leave (or try solve for C)
      let lhs0 := simplify (subst (subst lhs x x0) y y0)
      let rhs0 := simplify (subst (subst rhs x x0) y y0)
      -- lhs0 = rhs0 should constrain C: solve lhs0 - rhs0 = 0 for C
      match solveScalar (sub lhs0 rhs0) "C" with
      | .solutions [] => throw "dsolve IC: no value of C satisfies the condition"
      | .solutions (cVal :: _) =>
        pure (tidyODESol (eq lhs (simplify (subst rhs "C" cVal))))
      | .all => pure sol
      | .empty => throw "dsolve IC: inconsistent initial condition"
      | .unsupported msg => throw s!"dsolve IC: {msg}"
    else
      let fx0 := simplify (subst rhs x x0)
      -- y0 = f(x0, C) → f(x0,C) - y0 = 0
      match solveScalar (sub fx0 y0) "C" with
      | .solutions [] => throw "dsolve IC: no value of C satisfies the condition"
      | .solutions (cVal :: _) =>
        pure (tidyODESol (eq (var y) (simplify (subst rhs "C" cVal))))
      | .all => pure (tidyODESol sol)
      | .empty => throw "dsolve IC: inconsistent initial condition"
      | .unsupported msg => throw s!"dsolve IC: {msg}"

/-! ### Second-order constant-coefficient -/

/-- Decompose expression into real/imag rational parts when possible. -/
def asComplexParts? (e : Expr) : Option (RatConst × RatConst) :=
  match simplify e with
  | const c => some (c.re, c.im)
  | e =>
    -- Ground complex via re/im if both fold to rationals
    match simplify (re e), simplify (im e) with
    | const a, const b =>
      if a.im.isZero && b.im.isZero then some (a.re, b.re) else none
    | _, _ => none

/--
  Build real fundamental solutions for two characteristic roots.
  Returns basis functions of `x`.
-/
def constCoeffBasis2 (r1 r2 : Expr) (x : String) : List Expr :=
  let xv := var x
  let r1 := simplify r1
  let r2 := simplify r2
  if r1 == r2 then
    [exp (mul r1 xv), mul xv (exp (mul r1 xv))]
  else
    match asComplexParts? r1, asComplexParts? r2 with
    | some (a1, b1), some (a2, b2) =>
      -- Conjugate pair: a±bi
      if a1 == a2 && b1 == RatConst.neg b2 && !b1.isZero then
        let alpha := ofRat a1
        let beta := ofRat (if b1.num < 0 then RatConst.neg b1 else b1)
        let e := exp (mul alpha xv)
        if a1.isZero then
          [cos (mul beta xv), sin (mul beta xv)]
        else
          [mul e (cos (mul beta xv)), mul e (sin (mul beta xv))]
      else if a1 == a2 && b2 == RatConst.neg b1 && !b2.isZero then
        let alpha := ofRat a1
        let beta := ofRat (if b2.num < 0 then RatConst.neg b2 else b2)
        let e := exp (mul alpha xv)
        if a1.isZero then
          [cos (mul beta xv), sin (mul beta xv)]
        else
          [mul e (cos (mul beta xv)), mul e (sin (mul beta xv))]
      else
        [exp (mul r1 xv), exp (mul r2 xv)]
    | _, _ =>
      [exp (mul r1 xv), exp (mul r2 xv)]

/-- `arg` is `ω·x` with rational `ω`. -/
def omegaOfArg? (arg : Expr) (x : String) : Option RatConst :=
  let arg := simplify arg
  if arg == var x then some RatConst.one
  else
    match arg with
    | mul (const c) (var v) =>
      if v == x then CplxConst.toRat? c else none
    | mul (var v) (const c) =>
      if v == x then CplxConst.toRat? c else none
    | _ => none

/-- Match `K·sin(ωx)` / `K·cos(ωx)`. Returns `(amp, ω, isSin)`. -/
partial def matchTrigForce? (e : Expr) (x : String) : Option (Expr × RatConst × Bool) :=
  go (simplify e)
where
  go : Expr → Option (Expr × RatConst × Bool)
  | sin arg =>
    match omegaOfArg? arg x with
    | some w => some (one, w, true)
    | none => none
  | cos arg =>
    match omegaOfArg? arg x with
    | some w => some (one, w, false)
    | none => none
  | mul (const k) rest =>
    match go rest with
    | some (amp, w, s) => some (simplify (mul (const k) amp), w, s)
    | none => none
  | mul rest (const k) => go (mul (const k) rest)
  | _ => none

/-- `e` as `cc·cos(ωx) + sc·sin(ωx)`. -/
partial def collectSinCos (e : Expr) (wX : Expr) : Option (Expr × Expr) :=
  let e := simplify e
  if e == zero then some (zero, zero)
  else
    match e with
    | add a b =>
      match collectSinCos a wX, collectSinCos b wX with
      | some (c1, s1), some (c2, s2) =>
        some (simplify (add c1 c2), simplify (add s1 s2))
      | _, _ => none
    | mul (const k) rest =>
      match collectSinCos rest wX with
      | some (c, s) =>
        some (simplify (mul (const k) c), simplify (mul (const k) s))
      | none => none
    | mul rest (const k) => collectSinCos (mul (const k) rest) wX
    | cos arg =>
      if simplify arg == simplify wX then some (one, zero) else none
    | sin arg =>
      if simplify arg == simplify wX then some (zero, one) else none
    | _ => none

/-- Characteristic polynomial has roots `± iω` (simple resonance for sin/cos). -/
def trigResonance (a b c ω : RatConst) : Bool :=
  (b.isZero || ω.isZero) && (c == a * ω * ω) && !a.isZero

/--
  Undetermined coefficients for `A y''+B y'+C y = amp·sin/cos(ωx)`.
  Uses `x·(…)` on resonance.
-/
def particularTrig (a b c : RatConst) (amp : Expr) (ω : RatConst) (isSin : Bool)
    (x : String) : Option Expr :=
  let xv := var x
  let wX := if ω.isOne then xv else mul (ofRat ω) xv
  -- Resonance for y'' + ω²y (b=0, c=aω²):  ∓ (amp/(2aω)) x cos/sin
  if b.isZero && !ω.isZero && c == a * ω * ω then
    let den := ofRat (a * ω * RatConst.ofInt 2)
    if den == zero then none
    else
      let coef := if isSin then neg (div amp den) else div amp den
      let trig := if isSin then cos wX else sin wX
      some (simplify (mul (mul coef xv) trig))
  else
  let s : Nat := if trigResonance a b c ω then 1 else 0
  let UA := var "__ucA"
  let UB := var "__ucB"
  let body := add (mul UA (cos wX)) (mul UB (sin wX))
  let yp0 := if s == 0 then body else mul xv body
  let L :=
    simplify (add (add
      (mul (ofRat a) (diff (diff yp0 x) x))
      (mul (ofRat b) (diff yp0 x)))
      (mul (ofRat c) yp0))
  let target := if isSin then mul amp (sin wX) else mul amp (cos wX)
  let residual := simplify (sub L target)
  match collectSinCos residual wX with
  | none => none
  | some (cc, sc) =>
    match affineForm cc ["__ucA", "__ucB"], affineForm sc ["__ucA", "__ucB"] with
    | some (cA, c0), some (sA, s0) =>
      -- cA0 A + cA1 B = -c0 ;  sA0 A + sA1 B = -s0
      let M : Array (Array Expr) :=
        #[#[cA[0]!, cA[1]!], #[sA[0]!, sA[1]!]]
      let rhs : Array (Array Expr) :=
        #[#[simplify (neg c0)], #[simplify (neg s0)]]
      match Mat.solve M rhs with
      | .unique sol =>
        let Av := simplify (Mat.get! sol 0 0)
        let Bv := simplify (Mat.get! sol 1 0)
        let yp := subst (subst yp0 "__ucA" Av) "__ucB" Bv
        some (simplify yp)
      | _ => none
    | _, _ => none

/-- Variation of parameters for monic `y''+… = r` with basis `u1,u2`. -/
def variationOfParameters (u1 u2 r : Expr) (x : String) : Except String Expr := do
  let W := simplify (sub (mul u1 (diff u2 x)) (mul u2 (diff u1 x)))
  if W == zero then
    throw "dsolve: Wronskian vanished"
  else
    let v1' := simplify (neg (div (mul u2 r) W))
    let v2' := simplify (div (mul u1 r) W)
    let v1 ←
      match integrate v1' x with
      | .success F _ => pure (simplify F)
      | .notElementary msg => throw s!"dsolve: ∫ v1' not elementary: {msg}"
      | .failure msg => throw s!"dsolve: ∫ v1' failed: {msg}"
    let v2 ←
      match integrate v2' x with
      | .success F _ => pure (simplify F)
      | .notElementary msg => throw s!"dsolve: ∫ v2' not elementary: {msg}"
      | .failure msg => throw s!"dsolve: ∫ v2' failed: {msg}"
    pure (simplify (add (mul v1 u1) (mul v2 u2)))

/-- Particular solution for constant RHS: A y''+B y'+C y = G (G const). -/
def particularConst (A B C G : RatConst) (x : String) : Except String Expr :=
  if !C.isZero then
    match RatConst.div G C with
    | some k => pure (ofRat k)
    | none => throw "dsolve: division by zero in particular solution"
  else if !B.isZero then
    match RatConst.div G B with
    | some k => pure (mul (ofRat k) (var x))
    | none => throw "dsolve: division by zero in particular solution"
  else if !A.isZero then
    match RatConst.div G A with
    | some k =>
      match RatConst.div k (RatConst.ofInt 2) with
      | some k2 => pure (mul (ofRat k2) (pow (var x) (ofInt 2)))
      | none => throw "dsolve: internal error"
    | none => throw "dsolve: division by zero in particular solution"
  else
    throw "dsolve: degenerate second-order equation (A=B=C=0)"

/--
  Solve constant-coefficient second-order ODE
  `A y'' + B y' + C y + D = 0` with A,B,C rational, A ≠ 0.
  `D` may depend on `x` (forcing `g = −D`): undetermined coefficients
  for `sin`/`cos`, else variation of parameters.
-/
def dsolveConstCoeff2 (A B C D : Expr) (y x : String) : Except String Expr := do
  match asRatConstExpr? A, asRatConstExpr? B, asRatConstExpr? C with
  | some a, some b, some c =>
    if a.isZero then
      throw "dsolve: not second-order (coefficient of y'' is zero)"
    else
      let roots := quadraticRoots a b c
      if roots.isEmpty then
        throw "dsolve: could not solve characteristic equation"
      else
        let r1 := roots[0]!
        let r2 := if roots.length == 1 then roots[0]! else roots[1]!
        match constCoeffBasis2 r1 r2 x with
        | [u1, u2] =>
          let yh := simplify (add (mul (odeCi 0) u1) (mul (odeCi 1) u2))
          match asRatConstExpr? D with
          | some d =>
            if d.isZero then
              pure (tidyODESol (eq (var y) yh))
            else
              let G := RatConst.neg d
              let yp ← particularConst a b c G x
              pure (tidyODESol (eq (var y) (simplify (add yh yp))))
          | none =>
            -- A y''+B y'+C y = g  with g = −D
            match RatConst.inv a with
            | none => throw "dsolve: leading coefficient is zero"
            | some invA =>
              let g := simplify (neg D)
              let rMonic := simplify (mul (ofRat invA) g)
              let yp ←
                match matchTrigForce? g x with
                | some (amp, ω, isSin) =>
                  match particularTrig a b c amp ω isSin x with
                  | some yp => pure yp
                  | none => variationOfParameters u1 u2 rMonic x
                | none =>
                  variationOfParameters u1 u2 rMonic x
              pure (tidyODESol (eq (var y) (simplify (add yh yp))))
        | _ => throw "dsolve: expected 2 basis functions"
  | _, _, _ =>
    throw "dsolve: second-order solver requires constant rational coefficients"

/-- Try second-order constant-coeff path when y'' is present with constant A,B,C. -/
def dsolveSecondOrder? (e : Expr) (y x : String) : Option (Except String Expr) :=
  match odeResidual2 e y with
  | none => none
  | some (A, B, C, D) =>
    let A := simplify A
    if A == zero then none
    else
      match asRatConstExpr? A, asRatConstExpr? B, asRatConstExpr? C with
      | some a, some _, some _ =>
        if a.isZero then none
        else if dependsOnYFamily D y then none
        else some (dsolveConstCoeff2 A B C D y x)
      | _, _, _ => none

/-! ### Linear systems Y' = A Y via expm -/

/--
  Fundamental matrix Φ(x) = expm(A x) = P · exp(J x) · P⁻¹
  for constant A (Jordan form; includes defective matrices).
-/
def fundamentalMatrix (A : Array (Array Expr)) (x : String) : Except String (Array (Array Expr)) :=
  match Mat.expmAt A (var x) with
  | .ok Phi => pure Phi
  | .error msg => throw s!"dsolve: {msg}"

/-- Pack a solution column as named equations `y1 = …`, `y2 = …`. -/
def packYEqs (Y : Array (Array Expr)) : Expr :=
  let n := Mat.nrows Y
  let eqs : Array (Array Expr) :=
    Id.run do
      let mut out : Array (Array Expr) := Array.empty
      for i in [:n] do
        let yi := var s!"y{i + 1}"
        let val := simplify (Mat.get! Y i 0)
        out := out.push #[eq yi val]
      pure out
  simplify (Expr.mat eqs)

/--
  Solve the homogeneous linear system `Y' = A Y`.
  Returns named equations `yᵢ = (expm(A x) · C)ᵢ` with free constants `C1…Cn`.
-/
def dsolveLinSys (A : Array (Array Expr)) (x : String := "x") : Except String Expr :=
  let n := Mat.nrows A
  if n == 0 || n != Mat.ncols A then
    throw "dsolve: system matrix must be square and non-empty"
  else do
    let Phi ← fundamentalMatrix A x
    let Ccol : Array (Array Expr) :=
      Id.run do
        let mut rows : Array (Array Expr) := Array.empty
        for i in [:n] do
          rows := rows.push #[odeCi i]
        pure rows
    match Mat.mul Phi Ccol with
    | none => throw "dsolve: Φ·C shape error"
    | some Y => pure (packYEqs Y)

/-- Solve Y' = A Y with initial condition Y(0) = Y0 (column or row). -/
def dsolveLinSysIC (A : Array (Array Expr)) (Y0 : Array (Array Expr)) (x : String := "x") :
    Except String Expr :=
  let n := Mat.nrows A
  if n == 0 || n != Mat.ncols A then
    throw "dsolve: system matrix must be square"
  else
    let y0col : Option (Array (Array Expr)) :=
      if Mat.nrows Y0 == n && Mat.ncols Y0 == 1 then some Y0
      else if Mat.nrows Y0 == 1 && Mat.ncols Y0 == n then some (Mat.transpose Y0)
      else if Mat.nrows Y0 == n && Mat.ncols Y0 == n && n == 1 then some Y0
      else none
    match y0col with
    | none => throw s!"dsolve: initial vector must be {n}×1 (or 1×{n})"
    | some y0 => do
      let Phi ← fundamentalMatrix A x
      match Mat.mul Phi y0 with
      | none => throw "dsolve: Φ·Y0 shape error"
      | some Y => pure (packYEqs Y)

/--
  Solve an ODE for unknown `y(x)`.

  Order of attempts:
  1. Second-order constant-coefficient (`y''` / `ypp`)
  2. First-order linear (integrating factor)
  3. Separable first-order
-/
def dsolve (e : Expr) (y : String := "y") (x : String := "x") : Except String Expr :=
  -- Matrix argument → linear system Y' = A Y
  match asMat? (simplify e) with
  | some A => dsolveLinSys A x
  | none =>
    match dsolveSecondOrder? e y x with
    | some (.ok sol) => pure (tidyODESol sol)
    | some (.error err) =>
      match dsolveFirstOrder e y x with
      | .ok sol => pure sol
      | .error e2 => throw s!"{err}; also: {e2}"
    | none => dsolveFirstOrder e y x

/-- Solve ODE then apply y(x0)=y0. -/
def dsolveIC (e : Expr) (y x : String) (x0 y0 : Expr) : Except String Expr := do
  let sol ← dsolve e y x
  applyIC sol y x x0 y0

/--
  Apply two ICs y(x0)=y0, y'(x0)=yp0 to a second-order solution `y = f(x,C1,C2)`.
-/
def applyIC2 (sol : Expr) (y x : String) (x0 y0 yp0 : Expr) : Except String Expr :=
  match asEquation? sol with
  | none => throw "dsolve IC: expected explicit solution y = …"
  | some (lhs, rhs) =>
    if lhs != var y then throw "dsolve IC: expected y = …"
    else
      let fx0 := simplify (subst rhs x x0)
      let fpx := diff rhs x
      let fpx0 := simplify (subst fpx x x0)
      -- Solve the linear system in C1, C2:
      -- f(x0) = y0, f'(x0) = yp0
      -- Build two residuals and use solveLinearSystem
      let eq1 := eq fx0 y0
      let eq2 := eq fpx0 yp0
      match solveLinearSystem [eq1, eq2] (some ["C1", "C2"]) with
      | .error msg => throw s!"dsolve IC: {msg}"
      | .ok named =>
        match namedGet? named "C1", namedGet? named "C2" with
        | some c1, some c2 =>
          let rhs' := simplify (subst (subst rhs "C1" c1) "C2" c2)
          pure (tidyODESol (eq (var y) rhs'))
        | _, _ => throw "dsolve IC: could not extract C1, C2"

/-- Second-order IC: y(x0)=y0, y'(x0)=yp0. -/
def dsolveIC2 (e : Expr) (y x : String) (x0 y0 yp0 : Expr) : Except String Expr := do
  let sol ← dsolve e y x
  applyIC2 sol y x x0 y0 yp0

end Taschenrechner
