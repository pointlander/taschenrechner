/-
  Ordinary differential equations.

  * First-order linear:  y' + P(x) y = Q(x)   → integrating factor
  * Separable: y' = f(x) g(y)     → ∫ dy/g = ∫ f dx
  * Second-order constant-coeff: a y'' + b y' + c y = g  (g constant)
  * Linear systems: Y' = A Y  → Y = expm(A x) · C  (via diagonalization)
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
  Solve constant-coefficient second-order ODE:
  `A y'' + B y' + C y + D = 0` with A,B,C,D rational constants, A ≠ 0.
  Homogeneous (D=0) or constant forcing (−D).
-/
def dsolveConstCoeff2 (A B C D : Expr) (y x : String) : Except String Expr := do
  match asRatConstExpr? A, asRatConstExpr? B, asRatConstExpr? C, asRatConstExpr? D with
  | some a, some b, some c, some d =>
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
          if d.isZero then
            pure (tidyODESol (eq (var y) yh))
          else
            let G := RatConst.neg d
            let yp ← particularConst a b c G x
            pure (tidyODESol (eq (var y) (simplify (add yh yp))))
        | _ => throw "dsolve: expected 2 basis functions"
  | _, _, _, _ =>
    throw "dsolve: second-order solver requires constant rational coefficients"

/-- Try second-order constant-coeff path when y'' is present with constant coeffs. -/
def dsolveSecondOrder? (e : Expr) (y x : String) : Option (Except String Expr) :=
  match odeResidual2 e y with
  | none => none
  | some (A, B, C, D) =>
    let A := simplify A
    if A == zero then none
    else
      match asRatConstExpr? A, asRatConstExpr? B, asRatConstExpr? C, asRatConstExpr? D with
      | some a, some _, some _, some _ =>
        if a.isZero then none
        else some (dsolveConstCoeff2 A B C D y x)
      | _, _, _, _ => none

/-! ### Linear systems Y' = A Y via expm -/

/--
  Fundamental matrix Φ(x) = expm(A x) = P · exp(D x) · P⁻¹
  for constant diagonalizable A. Diagonalize A (not A·x) so eigenvalues stay constant.
-/
def fundamentalMatrix (A : Array (Array Expr)) (x : String) : Except String (Array (Array Expr)) :=
  match Mat.diagonalize A with
  | .defective msg => throw s!"dsolve: {msg}"
  | .error msg => throw s!"dsolve: {msg}"
  | .ok P D =>
    let xv := var x
    match Mat.mapDiagonal D (fun lam => simplify (exp (mul (simplify lam) xv))) with
    | none => throw "dsolve: bad diagonal in fundamental matrix"
    | some eDx =>
      let eDx := Mat.simpMat eDx
      match Mat.inv P with
      | none => throw "dsolve: modal matrix P is singular"
      | some Pinv =>
        let Pinv := Mat.simpMat Pinv
        match Mat.mul P eDx with
        | none => throw "dsolve: P·exp(Dx) shape error"
        | some Pe =>
          match Mat.mul Pe Pinv with
          | none => throw "dsolve: Φ shape error"
          | some Phi => pure (Mat.simpMat Phi)

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
      -- Fall through to first-order only if not clearly second-order
      match odeResidual e y x with
      | some _ =>
        -- first-order form also parses; try it
        match odeResidual e y x with
        | none => throw err
        | some (A, B, C) =>
          if !dependsOn B y && !dependsOn A y && !dependsOn C y then
            match dsolveLinear A B C y x with
            | .ok sol => pure (tidyODESol sol)
            | .error _ =>
              match dsolveSeparable A B C y x with
              | .ok sol => pure (tidyODESol sol)
              | .error e2 => throw s!"{err}; also: {e2}"
          else
            match dsolveSeparable A B C y x with
            | .ok sol => pure (tidyODESol sol)
            | .error e2 => throw s!"{err}; also: {e2}"
      | none => throw err
    | none =>
      match odeResidual e y x with
      | none =>
        throw "dsolve: expected ODE in y'/y or y''/y'/y (use y', yp, y'', ypp) or a square matrix A for Y'=A Y"
      | some (A, B, C) =>
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
