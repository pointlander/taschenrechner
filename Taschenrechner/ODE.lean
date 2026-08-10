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
        let sol := simplify (div num mu)
        pure (eq (var y) sol)
      | .notElementary r => throw s!"dsolve: ∫ μ·Q not elementary: {r}"
      | .failure r => throw s!"dsolve: ∫ μ·Q failed: {r}"
    | .notElementary r => throw s!"dsolve: ∫ P not elementary: {r}"
    | .failure r => throw s!"dsolve: ∫ P failed: {r}"

/--
  Separable: A(x) y' = f(x) * g(y) written as yp = f(x)*g(y),
  residual: yp − f*g = 0 → A=1, and B,C not linear.

  Detect yp + C(x,y) = 0 where C = −f(x)g(y).
  Try: C factors as −f(x)*g(y).
-/
def dsolveSeparable (A B C : Expr) (y x : String) : Except String Expr :=
  -- Require B = 0 (no naked y term) and A ≠ 0: yp = −C/A = f(x) g(y)
  if !isZeroExpr B x && dependsOn B y then
    throw "dsolve: not separable (linear y term present); try linear solver"
  else if isZeroExpr A x then
    throw "dsolve: missing y'"
  else
    let rhs := simplify (neg (div C A))  -- y' = rhs
    -- Factor rhs into f(x) * g(y) by splitting free vars
    match splitSeparable rhs x y with
    | none => throw "dsolve: could not separate variables"
    | some (f, g) =>
      -- ∫ dy/g(y) = ∫ f(x) dx
      if isZeroExpr g y then throw "dsolve: g(y) = 0"
      else
        let invG := simplify (div one g)
        match integrate invG y with
        | .success Gy _ =>
          match integrate f x with
          | .success Fx _ =>
            -- Gy = Fx + C  (implicit)
            pure (eq Gy (add Fx odeC))
          | .notElementary r => throw s!"dsolve: ∫ f(x) not elementary: {r}"
          | .failure r => throw s!"dsolve: ∫ f(x) failed: {r}"
        | .notElementary r => throw s!"dsolve: ∫ dy/g not elementary: {r}"
        | .failure r => throw s!"dsolve: ∫ dy/g failed: {r}"

where
  /-- Split product into factor depending only on x and only on y. -/
  splitSeparable (e : Expr) (x y : String) : Option (Expr × Expr) :=
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
  Solve a first-order ODE residual / equation for unknown `y(x)`.
  Tries linear integrating-factor form first, then separable.
-/
def dsolve (e : Expr) (y : String := "y") (x : String := "x") : Except String Expr :=
  match odeResidual e y x with
  | none => throw "dsolve: expected linear form in yp and y (use yp for y')"
  | some (A, B, C) =>
    -- Prefer linear if B may depend only on x
    if !dependsOn B y && !dependsOn A y && !dependsOn C y then
      match dsolveLinear A B C y x with
      | .ok sol => pure sol
      | .error _ =>
        dsolveSeparable A B C y x
    else
      dsolveSeparable A B C y x

end Taschenrechner
