/-
  Ordinary differential equations.

  * First-order linear:  y' + P(x) y = Q(x)   → integrating factor
  * Bernoulli: y' + P(x) y = Q(x) y^n        → v = y^{1−n} reduces to linear
  * Homogeneous: y' = f(y/x)                  → v = y/x reduces to separable
  * Exact: M dx + N dy = 0 when M_y = N_x     → F(x,y) = C (μ(x)/μ(y) if needed)
  * Separable: y' = f(x) g(y)     → ∫ dy/g = ∫ f dx
  * Second-order constant-coeff: a y'' + b y' + c y = g(x)
    (undetermined coefficients for sin/cos; else variation of parameters)
  * Cauchy–Euler: a x² y'' + b x y' + c y = g(x)  (indicial r(r−1)+b r+c=0;
    x^k / polynomial RHS via undetermined coefficients; else VoP)
  * Reduction of order: missing y → v=y'; missing x → y''=v dv/dy
  * Higher-order constant-coeff: aₙ y^{(n)}+…+a₀ y = g (g const; n≥3)
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
  * k-th derivative: `y` + k `p`s, k primes, or `dky` (e.g. `yppp` / `y'''` / `d3y`)
  * Example: `dsolve(yp + P*y = Q, y, x)`, `dsolve(y'' + y = 0)`
-/
def ypName : String := "yp"
def yppName : String := "ypp"

/-- Highest derivative order recognized in linear ODEs. -/
def maxYDerivOrder : Nat := 6

/-- Aliases for the k-th derivative of `y` (`k ≥ 1`). -/
def yDerivAliases (k : Nat) : List String :=
  if k == 0 then []
  else if k == 1 then [ypName, "y'", "dy"]
  else if k == 2 then [yppName, "y''", "d2y"]
  else
    let pees := String.ofList (List.replicate k 'p')
    let primes := String.ofList (List.replicate k '\'')
    [s!"y{pees}", s!"y{primes}", s!"d{k}y"]

def derivOrderOfName? (name : String) : Option Nat :=
  Id.run do
    for i in [:maxYDerivOrder] do
      let k := maxYDerivOrder - i
      if (yDerivAliases k).contains name then return some k
    none

private def isYpName (name : String) : Bool :=
  derivOrderOfName? name == some 1

private def isYppName (name : String) : Bool :=
  derivOrderOfName? name == some 2

def dependsOnYDerivGE (e : Expr) (k0 : Nat) : Bool :=
  Id.run do
    if k0 == 0 || k0 > maxYDerivOrder then return false
    for i in [:maxYDerivOrder - k0 + 1] do
      let k := k0 + i
      if (yDerivAliases k).any (fun n => dependsOn e n) then
        return true
    false

private def dependsOnYFamily (e : Expr) (y : String) : Bool :=
  dependsOn e y || dependsOnYDerivGE e 1

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
    match derivOrderOfName? name with
    | some 1 => some (one, zero, zero)
    | some _ => none
    | none =>
      if name == y then some (zero, one, zero)
      else some (zero, zero, var name)
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
    match derivOrderOfName? name with
    | some 2 => some (one, zero, zero, zero)
    | some 1 => some (zero, one, zero, zero)
    | some _ => none
    | none =>
      if name == y then some (zero, zero, one, zero)
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

/-- Zero coefficient vector for `y, y', …, y^{(max)}`. -/
def zeroYCoeffs : Array Expr :=
  Array.replicate (maxYDerivOrder + 1) zero

/--
  Linear form in `y, y', …, y^{(n)}`:
  returns `(cs, D)` for `Σ cs[k]·y^{(k)} + D = 0` (`cs.size = maxYDerivOrder+1`).
-/
partial def linearFormInYN (e : Expr) (y : String) : Option (Array Expr × Expr) :=
  let e := simplify e
  go e
where
  go : Expr → Option (Array Expr × Expr)
  | add a b =>
    match go a, go b with
    | some (c1, d1), some (c2, d2) =>
      some (c1.zipWith (fun u v => simplify (add u v)) c2, simplify (add d1 d2))
    | _, _ => none
  | mul (const c) rest =>
    match go rest with
    | some (cs, d) =>
      some (cs.map (fun u => simplify (mul (const c) u)), simplify (mul (const c) d))
    | none => none
  | mul rest (const c) => go (mul (const c) rest)
  | var name =>
    match derivOrderOfName? name with
    | some k =>
      if k > maxYDerivOrder then none
      else some (zeroYCoeffs.set! k one, zero)
    | none =>
      if name == y then some (zeroYCoeffs.set! 0 one, zero)
      else some (zeroYCoeffs, var name)
  | const c => some (zeroYCoeffs, const c)
  | e =>
    if dependsOnYFamily e y then
      match e with
      | mul a b =>
        let aY := dependsOnYFamily a y
        let bY := dependsOnYFamily b y
        if aY && !bY then
          match go a with
          | some (cs, dd) =>
            if dd == zero then
              some (cs.map (fun u => simplify (mul u b)), zero)
            else none
          | none => none
        else if bY && !aY then
          match go b with
          | some (cs, dd) =>
            if dd == zero then
              some (cs.map (fun u => simplify (mul u a)), zero)
            else none
          | none => none
        else none
      | _ => none
    else
      some (zeroYCoeffs, e)

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

/-! ### Homogeneous: y' = f(y/x) -/

def homVName : String := "__homv"

private def dependsOnYp (e : Expr) : Bool :=
  dependsOn e ypName || dependsOn e "y'" || dependsOn e "dy"

def dependsOnYpp (e : Expr) : Bool :=
  dependsOn e yppName || dependsOn e "y''" || dependsOn e "d2y"

/-- `A·y' + R = 0` with `A,R` free of `y'` (`R` may depend on `y`). -/
partial def linearInYp (e : Expr) (_y : String) : Option (Expr × Expr) :=
  let e := simplify e
  if dependsOnYpp e then none
  else go e
where
  go : Expr → Option (Expr × Expr)
  | add a b =>
    match go a, go b with
    | some (a1, r1), some (a2, r2) =>
      some (simplify (add a1 a2), simplify (add r1 r2))
    | _, _ => none
  | mul (const c) rest =>
    match go rest with
    | some (a, r) =>
      some (simplify (mul (const c) a), simplify (mul (const c) r))
    | none => none
  | mul rest (const c) => go (mul (const c) rest)
  | var name =>
    if isYppName name then none
    else if isYpName name then some (one, zero)
    else some (zero, var name)
  | const c => some (zero, const c)
  | e =>
    if dependsOnYp e then
      match e with
      | mul a b =>
        let aYp := dependsOnYp a
        let bYp := dependsOnYp b
        if aYp && !bYp then
          match go a with
          | some (aa, rr) =>
            if rr == zero || isZeroExpr rr "x" then
              some (simplify (mul aa b), zero)
            else none
          | none => none
        else if bYp && !aYp then go (mul b a)
        else none
      | _ => none
    else some (zero, e)

/-- Right-hand side of `y' = F(x,y)`, if the ODE is first-order in `y'`. -/
def firstOrderRhs? (e : Expr) (y : String) : Option Expr :=
  match linearInYp (equationToZero (simplify e)) y with
  | none => none
  | some (A, R) =>
    if A == zero || isZeroExpr A "x" then none
    else if dependsOnYp A || dependsOnYp R then none
    else some (simplify (neg (div R A)))

def ratOfInts (n d : Int) : Expr :=
  if d == 0 then zero
  else if d < 0 then ofRat ⟨-n, d.natAbs⟩
  else ofRat ⟨n, d.toNat⟩

/--
  Check `F(xᵢ,yᵢ) = f(yᵢ/xᵢ)` at integer samples (skips poles / unevaluable).
-/
def evalHomCheck (F f : Expr) (y x v : String) : Bool :=
  let samples : List (Int × Int) :=
    [(2, 1), (3, 1), (4, 1), (5, 2), (3, 2), (4, 3), (5, 3), (7, 2), (6, 1), (5, 1)]
  Id.run do
    let mut hits : Nat := 0
    for (x0, y0) in samples do
      if x0 == 0 then
        pure ()
      else
        let Fx := subst (subst F x (ofInt x0)) y (ofInt y0)
        let fv := subst f v (ratOfInts y0 x0)
        match eval? (simplify Fx), eval? (simplify fv) with
        | some a, some b =>
          if a == b then hits := hits + 1
          else return false
        | _, _ => pure ()
    pure (hits ≥ 2)

/--
  If `F(x,y)` is homogeneous of degree 0, return `f(v)` in `__homv`
  such that `F(x,y) = f(y/x)`.
-/
def asHomogeneousF? (F : Expr) (y x : String) : Option Expr :=
  let F := simplify F
  if dependsOnYp F then none
  else
    let v := homVName
    let F1 := simplify (subst (subst F x one) y (var v))
    if dependsOn F1 x then none
    else if evalHomCheck F F1 y x v then some F1
    else none

/--
  Homogeneous `y' = f(y/x)`: `v = y/x` gives `x v' = f(v) − v`,
  hence `dv/(f(v)−v) = dx/x`.
-/
def dsolveHomogeneous (e : Expr) (y x : String) : Except String Expr :=
  match firstOrderRhs? e y with
  | none => throw "dsolve: not first-order in y'"
  | some F =>
    match asHomogeneousF? F y x with
    | none => throw "dsolve: right-hand side is not homogeneous of degree 0"
    | some f =>
      let v := homVName
      let den := simplify (sub f (var v))
      if den == zero || isZeroExpr den v then
        pure (tidyODESol (eq (var y) (mul odeC (var x))))
      else
        let integrand := simplify (div one den)
        match integrate integrand v with
        | .success Gv _ =>
          let rhs := simplify (add (ln (var x)) odeC)
          let impl := explicitFromImplicit Gv rhs v
          match asEquation? impl with
          | some (lhs, vr) =>
            if lhs == var v then
              pure (tidyODESol (eq (var y) (mul vr (var x))))
            else
              match solveScalar (sub Gv rhs) v with
              | .solutions (val :: _) =>
                pure (tidyODESol (eq (var y) (mul (simplify val) (var x))))
              | _ =>
                let Gxy := subst Gv v (div (var y) (var x))
                pure (tidyODESol (eq Gxy rhs))
          | none =>
            match solveScalar (sub Gv rhs) v with
            | .solutions (val :: _) =>
              pure (tidyODESol (eq (var y) (mul (simplify val) (var x))))
            | _ =>
              let Gxy := subst Gv v (div (var y) (var x))
              pure (tidyODESol (eq Gxy rhs))
        | .notElementary r => throw s!"dsolve homogeneous: ∫ dv/(f−v) not elementary: {r}"
        | .failure r => throw s!"dsolve homogeneous: ∫ dv/(f−v) failed: {r}"

/-- Try homogeneous after another first-order method failed. -/
def orHomogeneous (e : Expr) (y x : String) : Except String Expr → Except String Expr
  | .ok sol => .ok sol
  | .error msg =>
    match dsolveHomogeneous e y x with
    | .ok sol => .ok sol
    | .error _ => .error msg

/-! ### Exact: M dx + N dy = 0 -/

def exactDelta (M N : Expr) (x y : String) : Expr :=
  simplify (sub (diff M y) (diff N x))

def isExactMN (M N : Expr) (x y : String) : Bool :=
  let d := exactDelta M N x y
  d == zero || isZeroExpr d x || isZeroExpr d y || equivNF (diff M y) (diff N x) x

/-- `e(keep, other)` is independent of `other` at integer samples. -/
def evalIndependentOf (e : Expr) (other keep : String) : Bool :=
  let samples : List (Int × Int × Int) :=
    [(2, 1, 3), (3, 1, 4), (4, 2, 5), (5, 1, 2), (3, 2, 4)]
  Id.run do
    let mut hits : Nat := 0
    for (k0, o1, o2) in samples do
      let e1 := subst (subst e keep (ofInt k0)) other (ofInt o1)
      let e2 := subst (subst e keep (ofInt k0)) other (ofInt o2)
      match eval? (simplify e1), eval? (simplify e2) with
      | some a, some b =>
        if a == b then hits := hits + 1
        else return false
      | _, _ => pure ()
    pure (hits ≥ 2)

/-- `e` does not depend on `other` (after simplify / normal form / eval). -/
def independentOfVar (e : Expr) (other keep : String) : Bool :=
  let e := simplify (Expr.normalForm e keep)
  (!dependsOn e other && !dependsOnYp e) || evalIndependentOf e other keep

/-- `exp(ln u) → u`, `exp(k ln u) → u^k`. -/
def simpIntegratingFactor (μ : Expr) : Expr :=
  match simplify μ with
  | exp (ln u) => simplify u
  | exp (mul (const c) (ln u)) =>
    match CplxConst.toRat? c with
    | some q =>
      if q == RatConst.negOne then simplify (div one u)
      else if q.den == 1 then simplify (pow u (ofInt q.num))
      else simplify μ
    | none => simplify μ
  | e => e

/-- Integrating factor `μ(x)` or `μ(y)` when `M_y − N_x` has the special form. -/
def integratingFactor? (M N : Expr) (x y : String) : Option Expr :=
  if isExactMN M N x y then some one
  else
    let Δ := exactDelta M N x y
    if Δ == zero || isZeroExpr Δ x then some one
    else
      let r := simplify (Expr.cancel (div Δ N))
      if independentOfVar r y x then
        match integrate r x with
        | .success iP _ => some (simpIntegratingFactor (exp iP))
        | _ => none
      else
        let s := simplify (Expr.cancel (div (neg Δ) M))
        if independentOfVar s x y then
          match integrate s y with
          | .success iP _ => some (simpIntegratingFactor (exp iP))
          | _ => none
        else none

/-- Evaluate `e(xᵢ,yᵢ)` at integer samples; true if it is 0 whenever defined. -/
def evalZeroXY (e : Expr) (x y : String) : Bool :=
  let samples : List (Int × Int) :=
    [(1, 1), (2, 1), (3, 2), (4, 1), (5, 3), (2, 3), (3, 1), (4, 3)]
  Id.run do
    let mut hits : Nat := 0
    for (x0, y0) in samples do
      let ev := subst (subst e x (ofInt x0)) y (ofInt y0)
      match eval? (simplify ev) with
      | some c =>
        if c.isZero then hits := hits + 1
        else return false
      | none => pure ()
    pure (hits ≥ 2)

/-- Algebraic zero in either free variable. -/
def isZeroXY (e : Expr) (x y : String) : Bool :=
  let e := simplify (expand e)
  e == zero || isZeroExpr e x || isZeroExpr e y
    || equivNF e zero x || equivNF e zero y
    || evalZeroXY e x y

def cancelZeroXY (e : Expr) (x y : String) : Expr :=
  let e := simplify (expand e)
  if isZeroXY e x y then zero
  else
    let n := simplify (Expr.normalForm e x)
    if isZeroXY n x y then zero
    else
      let n2 := simplify (Expr.normalForm e y)
      if isZeroXY n2 x y then zero else e

/-- Potential `F` with `F_x = M`, `F_y = N`. -/
def exactPotential (M N : Expr) (x y : String) : Except String Expr :=
  match integrate M x with
  | .success Mx _ =>
    let gp := cancelZeroXY (sub N (diff Mx y)) x y
    if gp == zero then
      pure (simplify Mx)
    else if independentOfVar gp y x then
      let c := simplify (subst gp y one)
      pure (simplify (add Mx (mul c (var y))))
    else
      match integrate gp y with
      | .success g _ => pure (simplify (add Mx g))
      | .notElementary msg => throw s!"dsolve exact: ∫ g'(y) not elementary: {msg}"
      | .failure msg => throw s!"dsolve exact: ∫ g'(y) failed: {msg}"
  | .notElementary _ =>
    match integrate N y with
    | .success Ny _ =>
      let hp := cancelZeroXY (sub M (diff Ny x)) x y
      if hp == zero then
        pure (simplify Ny)
      else if independentOfVar hp x y then
        let c := simplify (subst hp x one)
        pure (simplify (add Ny (mul c (var x))))
      else
        match integrate hp x with
        | .success h _ => pure (simplify (add Ny h))
        | .notElementary msg => throw s!"dsolve exact: ∫ h'(x) not elementary: {msg}"
        | .failure msg => throw s!"dsolve exact: ∫ h'(x) failed: {msg}"
    | .notElementary msg => throw s!"dsolve exact: ∫ N dy not elementary: {msg}"
    | .failure msg => throw s!"dsolve exact: ∫ N dy failed: {msg}"
  | .failure msg => throw s!"dsolve exact: ∫ M dx failed: {msg}"

/-- `N y' + M = 0` exact (or exact after `μ(x)` / `μ(y)`). Implicit `F(x,y) = C`. -/
def dsolveExact (e : Expr) (y x : String) : Except String Expr :=
  match linearInYp (equationToZero (simplify e)) y with
  | none => throw "dsolve: not first-order in y'"
  | some (N0, M0) =>
    if dependsOnYp N0 || dependsOnYp M0 then
      throw "dsolve: y' appears nonlinearly"
    else if N0 == zero || isZeroExpr N0 x then
      throw "dsolve exact: missing y' (N = 0)"
    else
      match integratingFactor? M0 N0 x y with
      | none => throw "dsolve: not exact and no μ(x)/μ(y) integrating factor"
      | some μ =>
        let M := simplify (mul μ M0)
        let N := simplify (mul μ N0)
        if !isExactMN M N x y then
          throw "dsolve exact: integrating factor did not make M_y = N_x"
        else do
          let F ← exactPotential M N x y
          pure (tidyODESol (eq F odeC))

/-- Try exact after another first-order method failed. -/
def orExact (e : Expr) (y x : String) : Except String Expr → Except String Expr
  | .ok sol => .ok sol
  | .error msg =>
    match dsolveExact e y x with
    | .ok sol => .ok sol
    | .error _ => .error msg

/-- First-order: linear, separable, Bernoulli, homogeneous, then exact. -/
def dsolveFirstOrder (e : Expr) (y x : String) : Except String Expr :=
  if dependsOnYDerivGE (equationToZero (simplify e)) 2 then
    throw "dsolve: equation contains y'' (or higher); not first-order"
  else
  match odeResidual e y x with
  | some (A, B, C) =>
    if !dependsOn B y && !dependsOn A y && !dependsOn C y then
      match dsolveLinear A B C y x with
      | .ok sol => pure (tidyODESol sol)
      | .error e1 =>
        orExact e y x <| orHomogeneous e y x <|
          match dsolveSeparable A B C y x with
          | .ok sol => .ok (tidyODESol sol)
          | .error _ =>
            match dsolveBernoulli e y x with
            | .ok sol => .ok sol
            | .error _ => .error e1
    else
      orExact e y x <| orHomogeneous e y x <|
        match dsolveSeparable A B C y x with
        | .ok sol => .ok (tidyODESol sol)
        | .error e2 =>
          match dsolveBernoulli e y x with
          | .ok sol => .ok sol
          | .error _ => .error e2
  | none =>
    match dsolveBernoulli e y x with
    | .ok sol => pure sol
    | .error eB =>
      match orExact e y x (orHomogeneous e y x (.error eB)) with
      | .ok sol => pure sol
      | .error _ =>
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
  let W := simplify (Expr.cancel (sub (mul u1 (diff u2 x)) (mul u2 (diff u1 x))))
  if W == zero then
    throw "dsolve: Wronskian vanished"
  else
    let v1' := simplify (Expr.cancel (neg (div (mul u2 r) W)))
    let v2' := simplify (Expr.cancel (div (mul u1 r) W))
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

/-! ### Second-order Cauchy–Euler -/

/-- `e` as a monomial `K · x^m` with rational `K, m` (including `m < 0`). -/
def matchMonomialX? (e : Expr) (x : String) : Option (RatConst × RatConst) :=
  match RatFn.ofExpr? (simplify (Expr.cancel e)) x with
  | none => none
  | some rf =>
    let rf := RatFn.simplify rf
    if rf.num.isZero then some (RatConst.zero, RatConst.zero)
    else
      let mon (p : Poly) : Bool :=
        let p := Poly.strip p
        if p.isZero then true
        else
          let d := p.deg.toNat
          (List.range d).all (fun k => (Poly.coeff p k).isZero)
      if mon rf.num && mon rf.den && !rf.den.isZero then
        match RatConst.div (Poly.lc rf.num) (Poly.lc rf.den) with
        | none => none
        | some K => some (K, RatConst.ofInt (rf.num.deg - rf.den.deg))
      else none

/-- `e · x^n` is a rational constant (used to read β/x and γ/x²). -/
def constTimesInvXn? (e : Expr) (x : String) (n : Nat) : Option RatConst :=
  let e := simplify e
  match asRatConstExpr? e with
  | some c =>
    if c.isZero || n == 0 then some c else none
  | none =>
    match matchMonomialX? e x with
    | some (K, m) =>
      if m == RatConst.neg (RatConst.ofInt n) then some K else none
    | none =>
      asRatConstExpr? (simplify (Expr.cancel (mul e (pow (var x) (ofInt n)))))

/--
  Monic Cauchy–Euler: `y'' + (β/x) y' + (γ/x²) y`.
  Matches `a x² y'' + b x y' + c y` and the divided form `y'' + (b/x) y' + (c/x²) y`.
-/
def cauchyEulerMonic? (A B C : Expr) (x : String) : Option (RatConst × RatConst) :=
  let A := simplify A
  if A == zero then none
  else
    match constTimesInvXn? (div B A) x 1, constTimesInvXn? (div C A) x 2 with
    | some β, some γ => some (β, γ)
    | _, _ => none

/-- `x^r`, with `x^0 → 1` and `x^1 → x`. -/
def eulerXPow (x : String) (r : Expr) : Expr :=
  let r := simplify r
  if r == zero then one
  else if r == one then var x
  else pow (var x) r

/-- Real fundamental solutions of a Cauchy–Euler indicial pair. -/
def cauchyEulerBasis2 (r1 r2 : Expr) (x : String) : List Expr :=
  let xv := var x
  let r1 := simplify r1
  let r2 := simplify r2
  if r1 == r2 then
    let u := eulerXPow x r1
    [u, mul u (ln xv)]
  else
    match asComplexParts? r1, asComplexParts? r2 with
    | some (a1, b1), some (a2, b2) =>
      let mk (alpha beta : RatConst) : List Expr :=
        let xa := eulerXPow x (ofRat alpha)
        let arg :=
          if beta.isOne then ln xv else mul (ofRat beta) (ln xv)
        if alpha.isZero then
          [cos arg, sin arg]
        else
          [mul xa (cos arg), mul xa (sin arg)]
      if a1 == a2 && b1 == RatConst.neg b2 && !b1.isZero then
        mk a1 (if b1.num < 0 then RatConst.neg b1 else b1)
      else if a1 == a2 && b2 == RatConst.neg b1 && !b2.isZero then
        mk a1 (if b2.num < 0 then RatConst.neg b2 else b2)
      else
        [eulerXPow x r1, eulerXPow x r2]
    | _, _ =>
      [eulerXPow x r1, eulerXPow x r2]

/--
  Particular solution of the monic Euler operator for forcing `K · x^m`.
  Ansatz `x^{m+2}`, times `ln x` / `(ln x)²` on indicial resonance.
-/
def particularEulerPower (β γ K m : RatConst) (x : String) : Expr :=
  let s := m + RatConst.ofInt 2
  let I_s := s * (s - RatConst.one) + β * s + γ
  let xs := eulerXPow x (ofRat s)
  if !I_s.isZero then
    match RatConst.div K I_s with
    | some a => simplify (mul (ofRat a) xs)
    | none => zero
  else
    let Ip := s + s + β - RatConst.one
    if !Ip.isZero then
      match RatConst.div K Ip with
      | some a => simplify (mul (ofRat a) (mul xs (ln (var x))))
      | none => zero
    else
      match RatConst.div K (RatConst.ofInt 2) with
      | some a =>
        simplify (mul (ofRat a) (mul xs (pow (ln (var x)) (ofInt 2))))
      | none => zero

/-- Undetermined coefficients when the monic forcing is a sum of monomials `K x^m`. -/
partial def particularEulerForce? (β γ : RatConst) (r : Expr) (x : String) : Option Expr :=
  let r := simplify (Expr.cancel r)
  match asPolynomialIn? r x with
  | some p =>
    let rec go (i : Nat) (acc : Expr) : Expr :=
      match p.coeffs[i]? with
      | none => simplify acc
      | some k =>
        if k.isZero then go (i + 1) acc
        else go (i + 1) (add acc (particularEulerPower β γ k (RatConst.ofInt i) x))
    some (go 0 zero)
  | none =>
    match r with
    | add a b =>
      match particularEulerForce? β γ a x, particularEulerForce? β γ b x with
      | some u, some v => some (simplify (add u v))
      | _, _ => none
    | _ =>
      match matchMonomialX? r x with
      | some (K, m) => some (particularEulerPower β γ K m x)
      | none => none

/--
  Solve Cauchy–Euler `A y'' + B y' + C y + D = 0` when
  `B/A = β/x` and `C/A = γ/x²` with rational β, γ.
-/
def dsolveCauchyEuler2 (A B C D : Expr) (y x : String) : Except String Expr := do
  match cauchyEulerMonic? A B C x with
  | none => throw "dsolve: not a Cauchy–Euler equation"
  | some (β, γ) =>
    let roots := quadraticRoots RatConst.one (β - RatConst.one) γ
    if roots.isEmpty then
      throw "dsolve: could not solve indicial equation"
    else
      let r1 := roots[0]!
      let r2 := if roots.length == 1 then roots[0]! else roots[1]!
      match cauchyEulerBasis2 r1 r2 x with
      | [u1, u2] =>
        let yh := simplify (add (mul (odeCi 0) u1) (mul (odeCi 1) u2))
        let g := simplify (neg D)
        if g == zero || (match asRatConstExpr? D with | some d => d.isZero | none => false) then
          pure (tidyODESol (eq (var y) yh))
        else
          let rMonic := simplify (Expr.cancel (div g A))
          let yp ←
            match particularEulerForce? β γ rMonic x with
            | some yp => pure yp
            | none => variationOfParameters u1 u2 rMonic x
          pure (tidyODESol (eq (var y) (simplify (add yh yp))))
      | _ => throw "dsolve: expected 2 basis functions"

/-! ### Reduction of order (missing y or missing x) -/

def redOrderVName : String := "__rov"
def redOrderVpName : String := "__rovp"

def substYpAll (e : Expr) (val : Expr) : Expr :=
  subst (subst (subst e ypName val) "y'" val) "dy" val

def substYppAll (e : Expr) (val : Expr) : Expr :=
  subst (subst (subst e yppName val) "y''" val) "d2y" val

/-- Reciprocal by inverting each product factor (`1/(C y) → (1/C)·(1/y)`). -/
def recipByFactors (e : Expr) : Expr :=
  let inv1 : Expr → Expr
    | pow a b => pow a (neg b)
    | t => pow t negOne
  let fs := flattenMul e
  match fs with
  | [] => one
  | t :: rest => rest.foldl (fun acc u => mul acc (inv1 u)) (inv1 t)

/-- Product of factors; empty product is `1`. -/
def foldMul1 : List Expr → Expr
  | [] => one
  | t :: rest => rest.foldl (fun a b => mul a b) t

/-- Split `e = c · f` with `c` independent of `v`. -/
def peelIndepFactor (e : Expr) (v : String) : Expr × Expr :=
  let fs := flattenMul e
  let indep := fs.filter (fun t => !dependsOn t v)
  let dep := fs.filter (fun t => dependsOn t v)
  if indep.isEmpty then (one, e)
  else (foldMul1 indep, foldMul1 dep)

/-- `e = a·v + b` with `a, b` independent of `v` and `a ≠ 0`. -/
def asAffineIndep? (e : Expr) (v : String) : Option (Expr × Expr) :=
  match affineForm (simplify e) [v] with
  | none => none
  | some (cs, b) =>
    if cs.size == 0 then none
    else
      let a := cs[0]!
      if a == zero || dependsOn a v || dependsOn b v then none
      else some (a, b)

/-- ∫ 1/(a v + b) dv = (1/a) ln(a v + b). -/
def integrateLinearDenom (e : Expr) (v : String) : Option Expr :=
  let base? : Option Expr :=
    match e with
    | pow base (const r) =>
      match CplxConst.toRat? r with
      | some q => if q == RatConst.negOne then some base else none
      | none => none
    | _ => none
  match base? with
  | none => none
  | some base =>
    match asAffineIndep? base v with
    | none => none
    | some (a, _) =>
      if a == zero then none
      else some (simplify (div (ln base) a))

/-- Integrate, peeling symbolic parameters and handling `1/(x+C)`. -/
partial def integrateParam (e : Expr) (v : String) : IntegrateResult :=
  if !dependsOn e v then
    .success (simplify (mul e (var v))) .heuristic
  else
    let (c, f) := peelIndepFactor e v
    if !(c == one) && f != e && dependsOn f v then
      match integrateParam f v with
      | .success F src => .success (simplify (mul c F)) src
      | other => other
    else
      match integrate f v with
      | .success F src => .success F src
      | .notElementary r => .notElementary r
      | .failure r =>
        match integrateLinearDenom f v with
        | none => .failure r
        | some F =>
          let d := simplify (diff F v)
          if d == f || equivNF d f v then .success (simplify F) .heuristic
          else .failure r

/-- Isolate `unk` from a first-order solution `unk = …` (or `F = C`). -/
def explicitUnknown? (sol : Expr) (unk : String) : Option Expr :=
  match asEquation? sol with
  | none => none
  | some (lhs, rhs) =>
    if lhs == var unk then some rhs
    else if rhs == var unk then some lhs
    else
      match solveScalar (sub lhs rhs) unk with
      | .solutions (val :: _) => some (simplify val)
      | _ => none

/-- Invert `Gy(y) = rhs` after ∫ dy/v, including `a ln y`. -/
def isolateYFromQuadrature (Gy rhs : Expr) (y : String) : Expr :=
  let Gy := simplify Gy
  let rhs := simplify rhs
  let fallback := explicitFromImplicit Gy rhs y
  let fromLn : Option Expr :=
    match Gy with
    | ln arg =>
      if arg == var y then some (eq (var y) (exp rhs)) else none
    | mul a (ln arg) =>
      if arg == var y && !dependsOn a y then
        some (eq (var y) (simplify (exp (div rhs a))))
      else none
    | mul (ln arg) a =>
      if arg == var y && !dependsOn a y then
        some (eq (var y) (simplify (exp (div rhs a))))
      else none
    | _ => none
  match fromLn with
  | some sol => tidyODESol sol
  | none =>
    match asEquation? fallback with
    | some (lhs, _) =>
      if lhs == var y then tidyODESol fallback
      else
        match solveScalar (sub Gy rhs) y with
        | .solutions (val :: _) => tidyODESol (eq (var y) (simplify val))
        | _ => tidyODESol fallback
    | none => tidyODESol fallback

/-- `dy/dx = v(y)`: if `v` is free of `y` then `y = v x + C2`, else ∫ dy/v = x + C2. -/
def yFromVofY (v : Expr) (y x : String) : Except String Expr :=
  let v := simplify v
  if v == zero || isZeroExpr v y then
    pure (tidyODESol (eq (var y) (odeCi 1)))
  else if !dependsOn v y then
    pure (tidyODESol (eq (var y) (simplify (add (mul v (var x)) (odeCi 1)))))
  else
    let invV := recipByFactors v
    match integrateParam invV y with
    | .success Gy _ =>
      pure (isolateYFromQuadrature Gy (add (var x) (odeCi 1)) y)
    | .notElementary msg =>
      throw s!"dsolve reduction of order: ∫ dy/y' not elementary: {msg}"
    | .failure msg =>
      throw s!"dsolve reduction of order: ∫ dy/y' failed: {msg}"

/-- Missing `y`: `F(x, y', y'') = 0` via `v = y'`, then `y = ∫ v dx + C2`. -/
def dsolveMissingY (e : Expr) (y x : String) : Except String Expr := do
  let e0 := equationToZero (simplify e)
  let reduced := substYppAll (substYpAll e0 (var redOrderVName)) (var ypName)
  let vsol ←
    match dsolveFirstOrder reduced redOrderVName x with
    | .ok s => pure s
    | .error msg => throw s!"dsolve reduction of order (missing y): {msg}"
  match explicitUnknown? vsol redOrderVName with
  | none => throw "dsolve reduction of order: could not solve for y'"
  | some v =>
    let v := simplify (subst v "C" (odeCi 0))
    if v == zero || isZeroExpr v x then
      pure (tidyODESol (eq (var y) (odeCi 1)))
    else
      match integrateParam v x with
      | .success F _ =>
        pure (tidyODESol (eq (var y) (simplify (add F (odeCi 1)))))
      | .notElementary msg =>
        throw s!"dsolve reduction of order: ∫ y' dx not elementary: {msg}"
      | .failure msg =>
        throw s!"dsolve reduction of order: ∫ y' dx failed: {msg}"

/-- Missing `x`: `F(y, y', y'') = 0` via `y'' = v dv/dy`, then `dy/dx = v(y)`. -/
def dsolveMissingX (e : Expr) (y x : String) : Except String Expr := do
  let e0 := equationToZero (simplify e)
  let withYpp := substYppAll e0 (mul (var redOrderVName) (var redOrderVpName))
  let withYp := substYpAll withYpp (var redOrderVName)
  let reduced := subst withYp redOrderVpName (var ypName)
  let vsol ←
    match dsolveFirstOrder reduced redOrderVName y with
    | .ok s => pure s
    | .error msg => throw s!"dsolve reduction of order (missing x): {msg}"
  match explicitUnknown? vsol redOrderVName with
  | none => throw "dsolve reduction of order: could not solve for y'"
  | some v =>
    yFromVofY (subst v "C" (odeCi 0)) y x

/-! ### Higher-order constant-coefficient -/

/-- `cs` as rational constants, or `none`. -/
def ratCoeffArray? (cs : Array Expr) : Option (Array RatConst) :=
  Id.run do
    let mut out : Array RatConst := Array.empty
    for c in cs do
      match asRatConstExpr? c with
      | none => return none
      | some q => out := out.push q
    some out

/-- Highest `k` with `as[k] ≠ 0`. -/
def leadingDerivOrder (as : Array RatConst) : Nat :=
  Id.run do
    let mut n : Nat := 0
    for i in [:as.size] do
      if !(as[i]!.isZero) then n := i
    pure n

/-- Characteristic roots with multiplicity via square-free factorization. -/
def charRootsWithMult (p : Poly) : List (Expr × Nat) :=
  let (_c, facs) := Poly.squareFreeFactor p
  facs.foldl (fun acc (s, m) =>
    acc ++ (rootsPoly s).map fun r => (simplify r, m)) []

/-- `1, x, …, x^{m-1}` times `e^{r x}` (`r = 0` → pure powers). -/
def realExpBasis (r : Expr) (m : Nat) (x : String) : List Expr :=
  let xv := var x
  let r := simplify r
  let e :=
    if r == zero then one
    else
      match asRatConstExpr? r with
      | some q => if q.isZero then one else exp (mul r xv)
      | none => exp (mul r xv)
  (List.range m).map fun k =>
    let xk := if k == 0 then one else pow xv (ofNat k)
    simplify (mul xk e)

/-- `x^k e^{α x} cos(β x)` and `sin`, `k = 0…m-1`. -/
def realTrigBasis (alpha beta : RatConst) (m : Nat) (x : String) : List Expr :=
  let xv := var x
  let wX := if beta.isOne then xv else mul (ofRat beta) xv
  let e :=
    if alpha.isZero then one else exp (mul (ofRat alpha) xv)
  let c0 := if alpha.isZero then cos wX else mul e (cos wX)
  let s0 := if alpha.isZero then sin wX else mul e (sin wX)
  (List.range m).foldl (fun acc k =>
    let xk := if k == 0 then one else pow xv (ofNat k)
    acc ++ [simplify (mul xk c0), simplify (mul xk s0)]) []

/-- Real fundamental solutions for characteristic roots with multiplicity. -/
def constCoeffBasisN (roots : List (Expr × Nat)) (x : String) : List Expr :=
  Id.run do
    let n := roots.length
    let mut used : Array Bool := Array.replicate n false
    let mut basis : List Expr := []
    for i in [:n] do
      if used[i]! then
        pure ()
      else
        let (r, m) := roots[i]!
        match asComplexParts? r with
        | some (a, b) =>
          if b.isZero then
            used := used.set! i true
            basis := basis ++ realExpBasis (ofRat a) m x
          else
            let mut found := false
            for j in [:n] do
              if !found && i != j && !used[j]! then
                let (r2, m2) := roots[j]!
                match asComplexParts? r2 with
                | some (a2, b2) =>
                  if a == a2 && b == RatConst.neg b2 && m == m2 then
                    used := used.set! i true
                    used := used.set! j true
                    let beta := if b.num < 0 then RatConst.neg b else b
                    basis := basis ++ realTrigBasis a beta m x
                    found := true
                | none => pure ()
            if !found then
              used := used.set! i true
              basis := basis ++ realExpBasis r m x
        | none =>
          used := used.set! i true
          basis := basis ++ realExpBasis r m x
    pure basis

/-- Particular solution when the RHS is a constant and `a_k` is the first nonzero coeff. -/
def particularConstN (as : Array RatConst) (G : RatConst) (x : String) : Except String Expr :=
  let rec go (k : Nat) : Except String Expr :=
    if h : k < as.size then
      if as[k].isZero then go (k + 1)
      else
        match RatConst.div G as[k] with
        | none => throw "dsolve: division by zero in particular solution"
        | some q =>
          if k == 0 then pure (ofRat q)
          else
            let kf := RatConst.ofInt (Int.ofNat (factNat k))
            match RatConst.div q kf with
            | none => throw "dsolve: division by zero in particular solution"
            | some qk =>
              pure (simplify (mul (ofRat qk) (pow (var x) (ofNat k))))
    else
      throw "dsolve: degenerate constant-coefficient equation"
  go 0

/-- Homogeneous solution `Σ Cᵢ uᵢ`. -/
def linearComboBasis (us : List Expr) : Expr :=
  Id.run do
    let mut acc : Expr := zero
    for i in [:us.length] do
      acc := add acc (mul (odeCi i) us[i]!)
    simplify acc

/--
  Constant-coefficient `Σ a_k y^{(k)} + D = 0` of order `n ≥ 3`.
  Homogeneous, or constant forcing.
-/
def dsolveConstCoeffN (as : Array RatConst) (D : Expr) (y x : String) : Except String Expr := do
  let n := leadingDerivOrder as
  if n < 3 then
    throw "dsolve: expected order ≥ 3"
  else if as[n]!.isZero then
    throw "dsolve: leading coefficient is zero"
  else
    let p : Poly := ⟨as.extract 0 (n + 1)⟩
    let roots := charRootsWithMult p
    let got := roots.foldl (fun acc (_, m) => acc + m) 0
    if got < n then
      throw "dsolve: could not solve characteristic equation"
    else
      let us := constCoeffBasisN roots x
      if us.length != n then
        throw s!"dsolve: expected {n} basis functions, got {us.length}"
      else
        let yh := linearComboBasis us
        match asRatConstExpr? D with
        | some d =>
          if d.isZero then
            pure (tidyODESol (eq (var y) yh))
          else
            let yp ← particularConstN as (RatConst.neg d) x
            pure (tidyODESol (eq (var y) (simplify (add yh yp))))
        | none =>
          if D == zero then
            pure (tidyODESol (eq (var y) yh))
          else
            throw "dsolve: higher-order const-coeff solver requires homogeneous or constant RHS"

/-- Try constant-coefficient of order ≥ 3. -/
def dsolveHigherOrder? (e : Expr) (y x : String) : Option (Except String Expr) :=
  match linearFormInYN (equationToZero (simplify e)) y with
  | none => none
  | some (cs, D) =>
    match ratCoeffArray? cs with
    | none => none
    | some as =>
      let n := leadingDerivOrder as
      if n < 3 then none
      else if dependsOnYFamily D y then none
      else some (dsolveConstCoeffN as D y x)

/-- Try reduction of order when `y''` is present and `y` or `x` is absent. -/
def dsolveReduceOrder? (e : Expr) (y x : String) : Option (Except String Expr) :=
  let e0 := equationToZero (simplify e)
  if !dependsOnYpp e0 then none
  else if !dependsOn e0 y then some (dsolveMissingY e y x)
  else if !dependsOn e0 x then some (dsolveMissingX e y x)
  else none

/-- Try second-order constant-coeff, Cauchy–Euler, then reduction of order. -/
def dsolveSecondOrder? (e : Expr) (y x : String) : Option (Except String Expr) :=
  match odeResidual2 e y with
  | none => dsolveReduceOrder? e y x
  | some (A, B, C, D) =>
    let A := simplify A
    if A == zero then
      dsolveReduceOrder? e y x
    else
      match asRatConstExpr? A, asRatConstExpr? B, asRatConstExpr? C with
      | some a, some _, some _ =>
        if a.isZero || dependsOnYFamily D y then
          dsolveReduceOrder? e y x
        else some (dsolveConstCoeff2 A B C D y x)
      | _, _, _ =>
        if !dependsOnYFamily D y then
          match cauchyEulerMonic? A B C x with
          | some _ => some (dsolveCauchyEuler2 A B C D y x)
          | none => dsolveReduceOrder? e y x
        else
          dsolveReduceOrder? e y x

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
  2. Second-order Cauchy–Euler (`a x² y'' + b x y' + c y`)
  3. Reduction of order (missing `y` or missing `x`)
  4. Higher-order constant-coefficient (`y'''` / `yppp` / `d3y`, …)
  5. First-order linear (integrating factor)
  6. Separable first-order
-/
def dsolve (e : Expr) (y : String := "y") (x : String := "x") : Except String Expr :=
  -- Matrix argument → linear system Y' = A Y
  match asMat? (simplify e) with
  | some A => dsolveLinSys A x
  | none =>
    match dsolveSecondOrder? e y x with
    | some (.ok sol) => pure (tidyODESol sol)
    | some (.error err) =>
      match dsolveHigherOrder? e y x with
      | some (.ok sol) => pure (tidyODESol sol)
      | some (.error eH) =>
        match dsolveFirstOrder e y x with
        | .ok sol => pure sol
        | .error e2 => throw s!"{err}; {eH}; also: {e2}"
      | none =>
        match dsolveFirstOrder e y x with
        | .ok sol => pure sol
        | .error e2 => throw s!"{err}; also: {e2}"
    | none =>
      match dsolveHigherOrder? e y x with
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
