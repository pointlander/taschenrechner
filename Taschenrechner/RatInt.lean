/-
  Integration of rational functions over ℚ(x) and K(x)
  (K a real multiquadratic field, e.g. ℚ(√2)) — the base case of Risch.

  Steps:
  1. Polynomial division
  2. Yun square-free factorization + Hermite reduction
  3. Logarithmic / arctangent part via partial fractions over ℚ or K
     and Rothstein–Trager residues (rational roots of the resultant) over ℚ
-/
import Taschenrechner.Poly
import Taschenrechner.AlgNum
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
  | .sin _ | .cos _ | .tan _ | .sinh _ | .cosh _ | .tanh _
  | .exp _ | .ln _ | .atan _ | .asin _ | .acos _ | .sec _ | .csc _ | .cot _
  | .factorial _ | .gamma _ | .floor _ | .ite _ _ _ | .abs _ | .re _ | .im _ | .conj _
  | .eq _ _ | .lt _ _ | .le _ _ | .mat _ => none

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

/--
  Partial fraction decomposition of proper `B/C` over the given monic
  irreducible factors of `C` (distinct; for square-free denominators).
  Returns list of `(A_i, F_i)` with `B/C = ∑ A_i/F_i` and `deg A_i < deg F_i`.
-/
def partialFractions (B C : Poly) (factors : List Poly) : Option (List (Poly × Poly)) :=
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

/-- Build `∑ (Poly.toExpr Ai / Poly.toExpr Fi)` in variable `v`. -/
def partialFractionsToExpr (parts : List (Poly × Poly)) (v : String) : Expr :=
  parts.foldl (fun acc (Ai, Fi) =>
    let term :=
      if Fi.isOne then Poly.toExpr Ai v
      else if Ai.isZero then Expr.zero
      else Expr.div (Poly.toExpr Ai v) (Poly.toExpr Fi v)
    if acc == Expr.zero then term else Expr.add acc term) Expr.zero

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
    let (_c, facs0) := factorOverQ C
    let facs := facs0.foldl (fun acc f =>
      if acc.any (· == f) then acc else acc ++ [f]) []
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

/-! ### Partial fractions (apart) -/

/--
  Partial fraction decomposition of a rational expression in `v`.

  Steps: simplify → polynomial division → Hermite (absorb repeated factors into
  a rational `G`) → PF of the square-free proper remainder when factors are
  degree ≤ 2 over ℚ.
-/
def apartQ (e : Expr) (v : String := "x") : Option Expr :=
  match RatFn.ofExpr? e v with
  | none => none
  | some r =>
    let r := RatFn.simplify r
    if r.den.isZero then none
    else if r.num.isZero then some Expr.zero
    else
      let (Q, R) := divMod (strip r.num) (strip r.den)
      let polyPart :=
        if Q.isZero then Expr.zero else Poly.toExpr Q v
      if R.isZero then some (Expr.simplify polyPart)
      else
        let (G, B, C) := hermiteReduce R r.den
        let gExpr := RatFn.toExpr G v
        let head :=
          if polyPart == Expr.zero then gExpr
          else if gExpr == Expr.zero then polyPart
          else Expr.add polyPart gExpr
        if B.isZero then some (Expr.simplify head)
        else
          let C := monic (strip C)
          let (_c, facs) := factorOverQ C
          -- Deduplicate equal factors (factorOverQ may repeat linears)
          let facs := facs.foldl (fun acc f =>
            if acc.any (· == f) then acc else acc ++ [f]) []
          if facs.isEmpty then
            some (Expr.simplify (Expr.add head (Expr.div (Poly.toExpr B v) (Poly.toExpr C v))))
          else if facs.any (fun f => f.deg > 2) then
            -- leave unsplit remainder
            some (Expr.simplify (Expr.add head (Expr.div (Poly.toExpr B v) (Poly.toExpr C v))))
          else
            match partialFractions B C facs with
            | some parts =>
              let pf := partialFractionsToExpr parts v
              some (Expr.simplify (Expr.add head pf))
            | none =>
              some (Expr.simplify (Expr.add head (Expr.div (Poly.toExpr B v) (Poly.toExpr C v))))

/-! ### Rational functions over K = AlgNum -/

/-- `(g, s, t)` with `s*a + t*b = g` over K[x]. -/
partial def egcdAlgPoly (a b : AlgPoly) : AlgPoly × AlgPoly × AlgPoly :=
  let rec go (a b s0 t0 s1 t1 : AlgPoly) (fuel : Nat) : AlgPoly × AlgPoly × AlgPoly :=
    match fuel with
    | 0 => (AlgPoly.strip a, s0, t0)
    | fuel'+1 =>
      let b := AlgPoly.strip b
      if b.isZero then (AlgPoly.strip a, s0, t0)
      else
        let (q, r) := AlgPoly.divMod a b
        go b r s1 t1 (AlgPoly.sub s0 (AlgPoly.mul q s1)) (AlgPoly.sub t0 (AlgPoly.mul q t1)) fuel'
  go (AlgPoly.strip a) (AlgPoly.strip b) AlgPoly.one AlgPoly.zero AlgPoly.zero AlgPoly.one 128

def modInverseAlg (a m : AlgPoly) : Option AlgPoly :=
  let (g, s, _) := egcdAlgPoly a m
  if g.isZero then none
  else if g.deg > 0 then none
  else
    match AlgNum.inv (AlgPoly.lc g) with
    | some inv => some (AlgPoly.strip (AlgPoly.scale inv (AlgPoly.modPoly s m)))
    | none => none

def integrateAlgPoly (p : AlgPoly) (v : String) : Expr :=
  let p := AlgPoly.strip p
  if p.isZero then Expr.zero
  else
    Id.run do
      let mut acc : Expr := Expr.zero
      for i in [:p.coeffs.size] do
        let c := p.coeffs[i]!
        if !c.isZero then
          let k := i + 1
          match AlgNum.div c (AlgNum.ofInt k) with
          | none => pure ()
          | some ck =>
            let xp :=
              if k == 1 then Expr.var v
              else Expr.pow (Expr.var v) (Expr.ofInt k)
            let term := if ck.isOne then xp else Expr.mul (AlgNum.toExpr ck) xp
            acc := Expr.add acc term
      pure (Expr.simplify acc)

/-- Solve `a x ≡ b (mod m)` for `deg x < deg m` over K. -/
def solveCongruenceAlg (a b m : AlgPoly) : Option AlgPoly :=
  let a := AlgPoly.modPoly a m
  let b := AlgPoly.modPoly b m
  let g := AlgPoly.gcd a m
  if !(AlgPoly.modPoly b g |>.isZero) then none
  else if g.deg == 0 then
    match modInverseAlg a m with
    | none => none
    | some inv => some (AlgPoly.strip (AlgPoly.modPoly (AlgPoly.mul inv b) m))
  else
    match AlgPoly.exactDiv a g, AlgPoly.exactDiv b g, AlgPoly.exactDiv m g with
    | some a', some b', some m' =>
      match modInverseAlg a' m' with
      | none => none
      | some inv => some (AlgPoly.strip (AlgPoly.modPoly (AlgPoly.mul inv b') m))
    | _, _, _ => none

/--
  Hermite reduction of proper A/D over K.
  Returns `(G, B, C)` where `A/D = G' + B/C` and `C` is square-free.
-/
partial def hermiteReduceK (A D : AlgPoly) : AlgRatFn × AlgPoly × AlgPoly :=
  let A := AlgPoly.strip A
  let D0 := AlgPoly.strip D
  if D0.isZero then (AlgRatFn.zero, A, AlgPoly.one)
  else
    let lead := AlgPoly.lc D0
    let D := AlgPoly.monic D0
    let A :=
      match AlgNum.inv lead with
      | some inv => AlgPoly.scale inv A
      | none => A
    let (_c, sfs) := AlgPoly.squareFreeFactor D
    let D := sfs.foldl (fun acc (s, m) => AlgPoly.mul acc (AlgPoly.powNat s m)) AlgPoly.one
    reduce A D sfs AlgRatFn.zero
where
  reduce (A D : AlgPoly) (sfs : List (AlgPoly × Nat)) (G : AlgRatFn) :
      AlgRatFn × AlgPoly × AlgPoly :=
    match sfs.find? (fun (_, m) => m ≥ 2) with
    | none =>
      let r := AlgRatFn.canceled ⟨A, D⟩
      (G, r.num, r.den)
    | some (V, m) =>
      let m1 := m - 1
      let Vm := AlgPoly.powNat V m
      let U := match AlgPoly.exactDiv D Vm with | some u => u | none => AlgPoly.one
      let UV' := AlgPoly.mul U (AlgPoly.differentiate V)
      match AlgNum.inv (AlgNum.ofInt m1) with
      | none => (G, A, D)
      | some invm1 =>
        let rhs := AlgPoly.scale (AlgNum.neg invm1) (AlgPoly.modPoly A V)
        match solveCongruenceAlg UV' rhs V with
        | none => (G, AlgPoly.strip A, AlgPoly.strip D)
        | some B =>
          let B := AlgPoly.strip B
          let Bp := AlgPoly.differentiate B
          let inner :=
            AlgPoly.sub (AlgPoly.mul Bp V)
              (AlgPoly.scale (AlgNum.ofInt m1) (AlgPoly.mul B (AlgPoly.differentiate V)))
          let numer := AlgPoly.sub A (AlgPoly.mul U inner)
          match AlgPoly.exactDiv numer V with
          | none => (G, AlgPoly.strip A, AlgPoly.strip D)
          | some Anew =>
            let Dnew := match AlgPoly.exactDiv D V with | some d => d | none => D
            let G := AlgRatFn.add G ⟨B, AlgPoly.powNat V m1⟩
            let sfs' :=
              sfs.map (fun (s, e) => if s == V then (s, e - 1) else (s, e))
                |>.filter (fun (_, e) => e > 0)
            reduce Anew Dnew sfs' G

/-- ∫ (a x + b) / (x² + p x + q) dx over K, irreducible quadratic (negative disc). -/
def integrateQuadraticK (a b p q : AlgNum) (v : String) : Option Expr :=
  let two := AlgNum.ofInt 2
  let halfA := match AlgNum.div a two with | some h => h | none => AlgNum.zero
  let F : AlgPoly := ⟨#[q, p, AlgNum.one]⟩
  let logPart : Expr :=
    if halfA.isZero then Expr.zero
    else Expr.mul (AlgNum.toExpr halfA) (Expr.ln (AlgPoly.toExpr F v))
  let k := AlgNum.sub b (AlgNum.mul halfA p)
  if k.isZero then some (Expr.simplify logPart)
  else
    let p2 := match AlgNum.div p two with | some h => h | none => AlgNum.zero
    let r := AlgNum.sub q (AlgNum.mul p2 p2)
    let disc := AlgNum.sub (AlgNum.mul p p) (AlgNum.scale (RatConst.ofInt 4) q)
    -- Real roots: caller should have split into linears.
    if (AlgPoly.splitQuadratic? ⟨#[q, p, AlgNum.one]⟩).isSome then none
    else if disc.isZero then none
    else
      match AlgNum.toRat? r with
      | some rq => if rq.num < 0 then none else continueAtan p2 r k logPart v
      | none => continueAtan p2 r k logPart v
where
  continueAtan (p2 r k : AlgNum) (logPart : Expr) (v : String) : Option Expr :=
    if r.isZero then none
    else
      let sExpr : Expr :=
        match AlgNum.sqrt? r with
        | some s => AlgNum.toExpr s
        | none => Taschenrechner.sqrt (AlgNum.toExpr r)
      let u := Expr.add (Expr.var v) (AlgNum.toExpr p2)
      let atanArg := Expr.div u sExpr
      let atanPart := Expr.div (Expr.atan atanArg) sExpr
      let term := Expr.mul (AlgNum.toExpr k) atanPart
      some (Expr.simplify (Expr.add logPart term))

/-- Integrate A/F with deg A < deg F, F monic, deg 1 or 2 over K. -/
def integrateSimpleFactorK (A F : AlgPoly) (v : String) : Option Expr :=
  let A := AlgPoly.strip A
  let F := AlgPoly.monic (AlgPoly.strip F)
  if F.deg == 1 then
    let c := AlgPoly.coeff A 0
    if c.isZero then some Expr.zero
    else
      let L := Expr.ln (AlgPoly.toExpr F v)
      some (Expr.simplify (if c.isOne then L else Expr.mul (AlgNum.toExpr c) L))
  else if F.deg == 2 then
    integrateQuadraticK (AlgPoly.coeff A 1) (AlgPoly.coeff A 0)
      (AlgPoly.coeff F 1) (AlgPoly.coeff F 0) v
  else
    none

/-- Partial fractions of proper `B/C` over distinct monic factors of `C`. -/
def partialFractionsK (B C : AlgPoly) (factors : List AlgPoly) :
    Option (List (AlgPoly × AlgPoly)) :=
  Id.run do
    let mut out : List (AlgPoly × AlgPoly) := []
    for Fi in factors do
      let Gi := match AlgPoly.exactDiv C Fi with | some g => g | none => AlgPoly.zero
      if Gi.isZero then return none
      match modInverseAlg Gi Fi with
      | none => return none
      | some invG =>
        out := (AlgPoly.strip (AlgPoly.modPoly (AlgPoly.mul B invG) Fi),
                AlgPoly.monic Fi) :: out
    pure (some out)

def partialFractionsToExprK (parts : List (AlgPoly × AlgPoly)) (v : String) : Expr :=
  parts.foldl (fun acc (Ai, Fi) =>
    let term :=
      if Fi.isOne then AlgPoly.toExpr Ai v
      else if Ai.isZero then Expr.zero
      else Expr.div (AlgPoly.toExpr Ai v) (AlgPoly.toExpr Fi v)
    if acc == Expr.zero then term else Expr.add acc term) Expr.zero

/-- Deduplicate monic factors, preserving order. -/
def uniqueAlgFacs (facs : List AlgPoly) : List AlgPoly :=
  facs.foldl (fun acc f =>
    let f := AlgPoly.monic (AlgPoly.strip f)
    if acc.any (· == f) then acc else acc ++ [f]) []

/--
  Partial fraction decomposition of a rational expression in `v` over K(x).
-/
def apartK (e : Expr) (v : String := "x") : Option Expr :=
  match AlgRatFn.ofExpr? (Expr.simplify e) v with
  | none => none
  | some r =>
    let r := AlgRatFn.canceled r
    if r.den.isZero then none
    else if r.num.isZero then some Expr.zero
    else
      let (Q, R) := AlgPoly.divMod (AlgPoly.strip r.num) (AlgPoly.strip r.den)
      let polyPart :=
        if Q.isZero then Expr.zero else AlgPoly.toExpr Q v
      if R.isZero then some (Expr.simplify polyPart)
      else
        let (G, B, C) := hermiteReduceK R r.den
        let gExpr := AlgRatFn.toExpr G v
        let head :=
          if polyPart == Expr.zero then gExpr
          else if gExpr == Expr.zero then polyPart
          else Expr.add polyPart gExpr
        if B.isZero then some (Expr.simplify head)
        else
          let C := AlgPoly.monic (AlgPoly.strip C)
          let (_c, facs) := AlgPoly.factorOverK C
          let facs := uniqueAlgFacs facs
          if facs.isEmpty then
            some (Expr.simplify (Expr.add head
              (Expr.div (AlgPoly.toExpr B v) (AlgPoly.toExpr C v))))
          else if facs.any (fun f => f.deg > 2) then
            some (Expr.simplify (Expr.add head
              (Expr.div (AlgPoly.toExpr B v) (AlgPoly.toExpr C v))))
          else
            match partialFractionsK B C facs with
            | some parts =>
              let pf := partialFractionsToExprK parts v
              some (Expr.simplify (Expr.add head pf))
            | none =>
              some (Expr.simplify (Expr.add head
                (Expr.div (AlgPoly.toExpr B v) (AlgPoly.toExpr C v))))

/-- ∫ (A/D) dx with A, D ∈ K[x]. -/
partial def integrateRationalAlgPoly (A D : AlgPoly) (v : String) : Option Expr :=
  if D.isZero then none
  else
    let (Q, R) := AlgPoly.divMod (AlgPoly.strip A) (AlgPoly.strip D)
    let polyPart := integrateAlgPoly Q v
    if R.isZero then some polyPart
    else
      let (G, B, C) := hermiteReduceK R D
      let gExpr := AlgRatFn.toExpr G v
      if B.isZero then
        some (Expr.simplify (Expr.add polyPart gExpr))
      else
        let C := AlgPoly.monic (AlgPoly.strip C)
        let (_c, facs0) := AlgPoly.factorOverK C
        let facs := uniqueAlgFacs facs0
        if facs.isEmpty || facs.any (fun f => f.deg > 2) then
          if C.deg == 2 then
            match integrateSimpleFactorK B C v with
            | some L => some (Expr.simplify (Expr.add polyPart (Expr.add gExpr L)))
            | none => none
          else none
        else
          match partialFractionsK B C facs with
          | none => none
          | some parts =>
            Id.run do
              let mut acc : Expr := Expr.zero
              let mut ok := true
              for (Ai, Fi) in parts do
                match integrateSimpleFactorK Ai Fi v with
                | none => ok := false
                | some e => acc := Expr.add acc e
              if ok then
                pure (some (Expr.simplify (Expr.add polyPart (Expr.add gExpr acc))))
              else if C.deg == 2 then
                match integrateSimpleFactorK B C v with
                | some L =>
                  pure (some (Expr.simplify (Expr.add polyPart (Expr.add gExpr L))))
                | none => pure none
              else pure none

/-- Integrate if `e` is rational in `v` over K(x). -/
def integrateRationalAlg (e : Expr) (v : String) : Option Expr :=
  match AlgRatFn.ofExpr? (Expr.simplify e) v with
  | none => none
  | some r =>
    let r := AlgRatFn.canceled r
    integrateRationalAlgPoly r.num r.den v

/-! ### Public integration API -/

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

/-- Integrate if `e` is rational in `v` over ℚ(x) or K(x). -/
def integrateRationalExpr (e : Expr) (v : String) : Option Expr :=
  match RatFn.ofExpr? e v with
  | some r =>
    let r := RatFn.simplify r
    match integrateRationalPoly r.num r.den v with
    | some F => some F
    | none => integrateRationalAlg e v
  | none => integrateRationalAlg e v

/--
  Partial fraction decomposition over ℚ(x) or K(x).
  Prefers the algebraic path so real quadratics split as `(x ± √d)`.
-/
def apart (e : Expr) (v : String := "x") : Option Expr :=
  match apartK e v with
  | some a => some a
  | none => apartQ e v

/-- `apart` with fallback to simplified input. -/
def apartOrSimplify (e : Expr) (v : String := "x") : Expr :=
  match apart e v with
  | some a => a
  | none => Expr.simplify e

end Taschenrechner
