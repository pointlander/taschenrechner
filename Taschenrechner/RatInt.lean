/-
  Integration of rational functions over ℚ(x) — the base case of the Risch algorithm.

  Steps:
  1. Polynomial division
  2. Yun square-free factorization + Hermite reduction
  3. Logarithmic / arctangent part via partial fractions over ℚ
     and Rothstein–Trager residues (rational roots of the resultant)
-/
import Taschenrechner.Poly
import Taschenrechner.Simplify

namespace Taschenrechner

open Poly

/-! ### Rational functions A/B ∈ ℚ(x) -/

structure RatFn where
  num : Poly
  den : Poly
  deriving Repr, Inhabited

namespace RatFn

def zero : RatFn := ⟨Poly.zero, Poly.one⟩
def ofPoly (p : Poly) : RatFn := ⟨p, Poly.one⟩

def simplify (r : RatFn) : RatFn :=
  let n := strip r.num
  let d := strip r.den
  if n.isZero then zero
  else if d.isZero then ⟨n, d⟩
  else
    let g := gcd n d
    let n := match exactDiv n g with | some q => q | none => n
    let d := match exactDiv d g with | some q => q | none => d
    match RatConst.inv (lc d) with
    | none => ⟨strip n, strip d⟩
    | some inv => ⟨strip (scale inv n), strip (scale inv d)⟩

def add (a b : RatFn) : RatFn :=
  simplify ⟨Poly.add (mul a.num b.den) (mul b.num a.den), mul a.den b.den⟩

def neg (a : RatFn) : RatFn := simplify ⟨Poly.neg a.num, a.den⟩
def mul (a b : RatFn) : RatFn := simplify ⟨Poly.mul a.num b.num, Poly.mul a.den b.den⟩

def toExpr (r : RatFn) (v : String) : Expr :=
  let r := simplify r
  if r.den.isOne then Poly.toExpr r.num v
  else Expr.div (Poly.toExpr r.num v) (Poly.toExpr r.den v)

/-- Parse a pure rational expression in variable `v`. -/
partial def ofExpr? (e : Expr) (v : String) : Option RatFn :=
  go (Expr.simplify e)
where
  go : Expr → Option RatFn
  | .const r =>
    match CplxConst.toRat? r with
    | some q => some (ofPoly (Poly.ofConst q))
    | none => none  -- non-real constant: not in ℚ(x)
  | .var name => if name == v then some ⟨Poly.X, Poly.one⟩ else none
  | .add a b =>
    match go a, go b with
    | some ra, some rb => some (add ra rb)
    | _, _ => none
  | .mul a b =>
    match go a, go b with
    | some ra, some rb => some (mul ra rb)
    | _, _ => none
  | .pow base (.const r) =>
    match CplxConst.toRat? r with
    | none => none
    | some q =>
      if q.den != 1 then none
      else
        match go base with
        | none => none
        | some rb =>
          if q.num ≥ 0 then
            let k := q.num.toNat
            some ⟨powNat rb.num k, powNat rb.den k⟩
          else
            let k := q.num.natAbs
            if rb.num.isZero then none
            else some (simplify ⟨powNat rb.den k, powNat rb.num k⟩)
  | .pow _ _ => none
  | .sin _ | .cos _ | .tan _ | .exp _ | .ln _ | .atan _ | .re _ | .im _ | .conj _ | .mat _ => none

end RatFn

/-! ### Extended Euclidean algorithm -/

/-- `(g, s, t)` with `s*a + t*b = g` (not necessarily monic g). -/
partial def egcdPoly (a b : Poly) : Poly × Poly × Poly :=
  let rec go (a b s0 t0 s1 t1 : Poly) (fuel : Nat) : Poly × Poly × Poly :=
    match fuel with
    | 0 => (strip a, s0, t0)
    | fuel'+1 =>
      let b := strip b
      if b.isZero then (strip a, s0, t0)
      else
        let (q, r) := divMod a b
        go b r s1 t1 (sub s0 (mul q s1)) (sub t0 (mul q t1)) fuel'
  go (strip a) (strip b) Poly.one Poly.zero Poly.zero Poly.one 128

def modInverse (a m : Poly) : Option Poly :=
  let (g, s, _) := egcdPoly a m
  if g.isZero then none
  else if g.deg > 0 then none
  else
    match RatConst.inv (lc g) with
    | some inv => some (strip (scale inv (modPoly s m)))
    | none => none

/-! ### Polynomial integration -/

def integratePoly (p : Poly) (v : String) : Expr :=
  let p := strip p
  if p.isZero then Expr.zero
  else
    Id.run do
      let mut acc : Expr := Expr.zero
      for i in [:p.coeffs.size] do
        let c := p.coeffs[i]!
        if !c.isZero then
          let k := i + 1
          match RatConst.div c (RatConst.ofInt k) with
          | none => pure ()
          | some ck =>
            let xp :=
              if k == 1 then Expr.var v
              else Expr.pow (Expr.var v) (Expr.ofInt k)
            let term := if ck.isOne then xp else Expr.mul (Expr.ofRat ck) xp
            acc := Expr.add acc term
      pure (Expr.simplify acc)

/-! ### Hermite reduction -/

/-- Solve `a x ≡ b (mod m)` for `deg x < deg m`. -/
def solveCongruence (a b m : Poly) : Option Poly :=
  let a := modPoly a m
  let b := modPoly b m
  let g := gcd a m
  if !(modPoly b g |>.isZero) then none
  else if g.deg == 0 then
    match modInverse a m with
    | none => none
    | some inv => some (strip (modPoly (mul inv b) m))
  else
    -- reduce by g when g|b
    match exactDiv a g, exactDiv b g, exactDiv m g with
    | some a', some b', some m' =>
      match modInverse a' m' with
      | none => none
      | some inv => some (strip (modPoly (mul inv b') m))
    | _, _, _ => none

/--
  Hermite reduction of proper A/D.
  Returns `(G, B, C)` where `A/D = G' + B/C` and `C` is square-free.
-/
partial def hermiteReduce (A D : Poly) : RatFn × Poly × Poly :=
  let A := strip A
  let D0 := strip D
  if D0.isZero then (RatFn.zero, A, Poly.one)
  else
    let lead := lc D0
    let D := monic D0
    -- A_adj so A/D0 = A_adj/D with monic D
    let A :=
      match RatConst.inv lead with
      | some inv => scale inv A
      | none => A
    let (_c, sfs) := squareFreeFactor D
    -- rebuild D as product s_i^i
    let D := sfs.foldl (fun acc (s, m) => mul acc (powNat s m)) Poly.one
    reduce A D sfs RatFn.zero
where
  reduce (A D : Poly) (sfs : List (Poly × Nat)) (G : RatFn) : RatFn × Poly × Poly :=
    match sfs.find? (fun (_, m) => m ≥ 2) with
    | none =>
      let r := RatFn.simplify ⟨A, D⟩
      (G, r.num, r.den)
    | some (V, m) =>
      let m1 := m - 1
      let Vm := powNat V m
      let U := match exactDiv D Vm with | some u => u | none => Poly.one
      let UV' := mul U (differentiate V)
      match RatConst.inv (RatConst.ofInt m1) with
      | none => (G, A, D)
      | some invm1 =>
        -- B * (U V') ≡ -A/(m-1)  (mod V)
        let rhs := scale (RatConst.neg invm1) (modPoly A V)
        match solveCongruence UV' rhs V with
        | none => (G, strip A, strip D)
        | some B =>
          let B := strip B
          let Bp := differentiate B
          let inner := sub (mul Bp V) (scale (RatConst.ofInt m1) (mul B (differentiate V)))
          let numer := sub A (mul U inner)
          match exactDiv numer V with
          | none => (G, strip A, strip D)
          | some Anew =>
            let Dnew := match exactDiv D V with | some d => d | none => D
            let G := RatFn.add G ⟨B, powNat V m1⟩
            let sfs' :=
              sfs.map (fun (s, e) => if s == V then (s, e - 1) else (s, e))
                |>.filter (fun (_, e) => e > 0)
            reduce Anew Dnew sfs' G

/-! ### Log / atan part -/

/-- ∫ (a x + b) / (x² + p x + q) dx with irreducible (or general) quadratic. -/
def integrateQuadratic (a b p q : RatConst) (v : String) : Option Expr :=
  -- (a/2) ln(x²+px+q) + k ∫ dx/((x+p/2)² + r)
  let halfA := match RatConst.div a (RatConst.ofInt 2) with | some h => h | none => RatConst.zero
  let F : Poly := ⟨#[q, p, RatConst.one]⟩
  let logPart : Expr :=
    if halfA.isZero then Expr.zero
    else Expr.mul (Expr.ofRat halfA) (Expr.ln (Poly.toExpr F v))
  let k := b - halfA * p
  if k.isZero then some (Expr.simplify logPart)
  else
    let p2 := match RatConst.div p (RatConst.ofInt 2) with | some h => h | none => RatConst.zero
    let r := q - p2 * p2  -- (x + p/2)² + r
    -- r = (4q - p²)/4; sign of (4q-p²) = -disc
    let disc := p * p - RatConst.ofInt 4 * q
    if disc.num > 0 then
      -- two real roots — should have been split into linears
      none
    else if disc.isZero then
      -- repeated root:  k / (x+p/2)  after reduction → already Hermite's job
      none
    else
      -- r > 0 in the completed square sense when disc < 0
      -- ∫ dx / ((x+p/2)² + s²) = (1/s) atan((x+p/2)/s), s = sqrt(r)
      -- r = q - (p/2)² > 0 when disc < 0
      if !(r.num > 0 && r.den > 0) then none
      else
        -- s = √r; if r is a perfect square of a rational, exact; else keep sqrt in expr
        let sExpr : Expr :=
          match perfectSqrt r with
          | some s => Expr.ofRat s
          | none => Taschenrechner.sqrt (Expr.ofRat r)
        let u := Expr.add (Expr.var v) (Expr.ofRat p2)  -- x + p/2
        let atanArg := Expr.div u sExpr
        let atanPart := Expr.div (Expr.atan atanArg) sExpr
        let term := Expr.mul (Expr.ofRat k) atanPart
        some (Expr.simplify (Expr.add logPart term))
where
  perfectSqrt (r : RatConst) : Option RatConst :=
    let r := RatConst.normalize r
    if r.num < 0 then none
    else
      let n := r.num.toNat
      let d := r.den
      match natSqrtExact n, natSqrtExact d with
      | some sn, some sd => some (RatConst.normalize ⟨(sn : Int), sd⟩)
      | _, _ => none
  natSqrtExact (n : Nat) : Option Nat :=
    if n == 0 then some 0
    else
      Id.run do
        let mut i : Nat := 1
        while i * i < n do i := i + 1
        if i * i == n then pure (some i) else pure none

/-- Integrate A/F with deg A < deg F, F monic, deg 1 or 2 (or RT). -/
def integrateSimpleFactor (A F : Poly) (v : String) : Option Expr :=
  let A := strip A
  let F := monic (strip F)
  if F.deg == 1 then
    let c := coeff A 0
    if c.isZero then some Expr.zero
    else
      let L := Expr.ln (Poly.toExpr F v)
      some (Expr.simplify (if c.isOne then L else Expr.mul (Expr.ofRat c) L))
  else if F.deg == 2 then
    integrateQuadratic (coeff A 1) (coeff A 0) (coeff F 1) (coeff F 0) v
  else
    none

/-- Rothstein–Trager for rational residues. -/
partial def rothsteinTrager (B C : Poly) (v : String) : Option Expr :=
  let B := strip B
  let C := monic (strip C)
  if C.deg ≤ 0 then some (integratePoly B v)
  else
    let Cp := differentiate C
    let R := resultantPolyInZ B C Cp
    let roots :=
      (rationalRootCandidates R).filter fun z => (eval R z).isZero
    -- Always try linear factors of C as well
    let (_c, facs) := factorOverQ C
    Id.run do
      let mut acc : Expr := Expr.zero
      let mut ok := true
      if !facs.isEmpty && facs.all (fun f => f.deg ≤ 2) then
        match partialFractions B C facs with
        | none => pure ()
        | some parts =>
          for (Ai, Fi) in parts do
            match integrateSimpleFactor Ai Fi v with
            | none => ok := false
            | some e => acc := Expr.add acc e
          if ok then return some (Expr.simplify acc)
      -- RT rational residues
      acc := Expr.zero
      ok := true
      if roots.isEmpty then
        -- last chance: single quadratic factor
        if C.deg == 2 then
          return integrateSimpleFactor B C v
        else return none
      let mut seen : List RatConst := []
      for c in roots do
        if seen.any (· == c) then pure ()
        else
          seen := c :: seen
          let vc := gcd C (sub B (scale c Cp))
          if vc.deg ≥ 1 then
            let L := Expr.ln (Poly.toExpr (monic vc) v)
            let term := if c.isOne then L else Expr.mul (Expr.ofRat c) L
            acc := Expr.add acc term
          else ok := false
      if ok then pure (some (Expr.simplify acc)) else pure none
where
  partialFractions (B C : Poly) (factors : List Poly) : Option (List (Poly × Poly)) :=
    Id.run do
      let mut out : List (Poly × Poly) := []
      for Fi in factors do
        let Gi := match exactDiv C Fi with | some g => g | none => Poly.zero
        if Gi.isZero then return none
        match modInverse Gi Fi with
        | none => return none
        | some invG =>
          out := (strip (modPoly (mul B invG) Fi), monic Fi) :: out
      pure (some out)

  resultantPolyInZ (B C Cp : Poly) : Poly :=
    let n := max 0 C.deg.toNat
    let degBound := n + 2
    let pts := Id.run do
      let mut pts : List (RatConst × RatConst) := []
      for i in [0:degBound + 1] do
        let z := RatConst.ofInt (i : Int)
        let poly := sub B (scale z Cp)
        pts := (z, res C poly) :: pts
      pure pts
    interpolate pts

  interpolate (pts : List (RatConst × RatConst)) : Poly :=
    pts.foldl (fun acc (xj, yj) =>
      if yj.isZero then acc
      else
        let (num, den) :=
          pts.foldl (fun (n, d) (xi, _) =>
            if xi == xj then (n, d)
            else (mul n ⟨#[RatConst.neg xi, RatConst.one]⟩, d * (xj - xi)))
            (Poly.one, RatConst.one)
        match RatConst.inv den with
        | none => acc
        | some invd => add acc (scale (yj * invd) num)
    ) Poly.zero

/-! ### Public API -/

/-- ∫ (A/D) dx with A,D ∈ ℚ[x]. -/
partial def integrateRationalPoly (A D : Poly) (v : String) : Option Expr :=
  if D.isZero then none
  else
    let (Q, R) := divMod (strip A) (strip D)
    let polyPart := integratePoly Q v
    if R.isZero then some polyPart
    else
      let (G, B, C) := hermiteReduce R D
      let gExpr := RatFn.toExpr G v
      if B.isZero then
        some (Expr.simplify (Expr.add polyPart gExpr))
      else
        match rothsteinTrager B C v with
        | some L => some (Expr.simplify (Expr.add polyPart (Expr.add gExpr L)))
        | none => none

/-- Integrate if `e` is rational in `v`. -/
def integrateRationalExpr (e : Expr) (v : String) : Option Expr :=
  match RatFn.ofExpr? e v with
  | none => none
  | some r =>
    let r := RatFn.simplify r
    integrateRationalPoly r.num r.den v

end Taschenrechner
