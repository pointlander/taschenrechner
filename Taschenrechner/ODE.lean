/-
  First-order ordinary differential equations.

  * Linear:  y' + P(x) y = Q(x)   → integrating factor
  * Separable: y' = f(x) g(y)     → ∫ dy/g = ∫ f dx  (when both integrate)
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Integrate
import Taschenrechner.Normal
import Taschenrechner.Eval
import Taschenrechner.Solve

namespace Taschenrechner

open Expr
open Taschenrechner.Expr (flattenMul)

/-- Arbitrary constant of integration in ODE solutions. -/
def odeC : Expr := var "C"

/--
  Represent y' as the free variable `yp` (or `y'` / `dy`) by convention, and y as `y`.

  * Dependent unknown is `y` (function of `x`)
  * Its derivative is free var `yp`  (aliases `y'`, `dy`)
  * Example: `dsolve(yp + P*y = Q, y, x)`
-/
def ypName : String := "yp"

private def isYpName (name : String) : Bool :=
  name == ypName || name == "y'" || name == "dy"

/-- Collect coefficient of `yp` and of `y` in a linear expression in those symbols. -/
partial def linearFormInY (e : Expr) (y : String) (_x : String) : Option (Expr × Expr × Expr) :=
  -- Returns (A, B, C) for A*yp + B*y + C = 0 with A,B,C independent of y, yp
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
    if isYpName name then
      some (one, zero, zero)
    else if name == y then
      some (zero, one, zero)
    else
      some (zero, zero, var name)
  | const c => some (zero, zero, const c)
  | e =>
    if dependsOn e y || dependsOn e ypName || dependsOn e "y'" || dependsOn e "dy" then
      -- try product: c(x)*y or c(x)*yp
      match e with
      | mul a b =>
        let aY := dependsOn a y || dependsOn a ypName || dependsOn a "y'" || dependsOn a "dy"
        let bY := dependsOn b y || dependsOn b ypName || dependsOn b "y'" || dependsOn b "dy"
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

/-- Rewrite equation to residual A*yp + B*y + C (= 0). -/
def odeResidual (e : Expr) (y x : String) : Option (Expr × Expr × Expr) :=
  let e := equationToZero (simplify e)
  linearFormInY e y x

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
  | sin e => sin (tidyExpForm e)
  | cos e => cos (tidyExpForm e)
  | tan e => tan (tidyExpForm e)
  | ln e => ln (tidyExpForm e)
  | atan e => atan (tidyExpForm e)
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

/--
  Solve a first-order ODE residual / equation for unknown `y(x)`.
  Tries linear integrating-factor form first, then separable.
-/
def dsolve (e : Expr) (y : String := "y") (x : String := "x") : Except String Expr :=
  match odeResidual e y x with
  | none => throw "dsolve: expected linear form in y' and y (use y' or yp for the derivative)"
  | some (A, B, C) =>
    -- Prefer linear if B may depend only on x
    if !dependsOn B y && !dependsOn A y && !dependsOn C y then
      match dsolveLinear A B C y x with
      | .ok sol => pure (tidyODESol sol)
      | .error _ =>
        match dsolveSeparable A B C y x with
        | .ok sol => pure (tidyODESol sol)
        | .error e => throw e
    else
      match dsolveSeparable A B C y x with
      | .ok sol => pure (tidyODESol sol)
      | .error e => throw e

/-- Solve ODE then apply y(x0)=y0. -/
def dsolveIC (e : Expr) (y x : String) (x0 y0 : Expr) : Except String Expr := do
  let sol ← dsolve e y x
  applyIC sol y x x0 y0

end Taschenrechner
