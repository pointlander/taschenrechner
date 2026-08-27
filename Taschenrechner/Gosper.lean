/-
  Gosper's algorithm: hypergeometric indefinite summation.

  A term `t(k)` is hypergeometric when `t(k+1)/t(k)` is rational in `k`.
  If a hypergeometric antidifference `s` exists (`s(k+1) − s(k) = t(k)`),
  then `∑_{k=lo}^{hi} t(k) = s(hi+1) − s(lo)`.

  Caps on shift / degree keep compile-time `#guard`s bounded.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Normal
import Taschenrechner.Eval
import Taschenrechner.LinAlg

namespace Taschenrechner

open Expr

def gosperMaxShift : Nat := 16
def gosperMaxDeg : Nat := 12

/-- `t(k) = rat(k) · geom^k` with `geom` free of `k`. -/
structure HypTerm where
  rat  : RatFn
  geom : Expr
  deriving Repr

namespace HypTerm

def mulH (a b : HypTerm) : HypTerm :=
  ⟨RatFn.mul a.rat b.rat, simplify (Expr.mul a.geom b.geom)⟩

end HypTerm

/-- `e = a·k + b` with `a,b` free of `k`. -/
partial def splitAffine (e : Expr) (k : String) : Option (Expr × Expr) :=
  go (simplify e)
where
  go : Expr → Option (Expr × Expr)
  | add a b =>
    match go a, go b with
    | some (a1, b1), some (a2, b2) =>
      some (simplify (add a1 a2), simplify (add b1 b2))
    | _, _ => none
  | mul (const c) rest =>
    match go rest with
    | some (a, b) =>
      some (simplify (mul (const c) a), simplify (mul (const c) b))
    | none => none
  | mul rest (const c) => go (mul (const c) rest)
  | var name =>
    if name == k then some (one, zero) else some (zero, var name)
  | const c => some (zero, const c)
  | e =>
    if dependsOn e k then
      match e with
      | mul a b =>
        let aK := dependsOn a k
        let bK := dependsOn b k
        if aK && !bK then
          match go a with
          | some (ca, ka) =>
            if ka == zero then some (simplify (mul ca b), zero) else none
          | none => none
        else if bK && !aK then go (mul b a)
        else none
      | _ => none
    else some (zero, e)

/-- Parse a hypergeometric term in index `k`. -/
partial def asHypTerm? (e : Expr) (k : String) : Option HypTerm :=
  let e := simplify e
  match RatFn.ofExpr? e k with
  | some r => some ⟨RatFn.simplify r, one⟩
  | none => factor e
where
  factor : Expr → Option HypTerm
  | mul a b =>
    match factor a, factor b with
    | some ta, some tb => some (HypTerm.mulH ta tb)
    | _, _ => none
  | add a b =>
    match factor a, factor b with
    | some ta, some tb =>
      if simplify ta.geom == simplify tb.geom then
        some ⟨RatFn.add ta.rat tb.rat, ta.geom⟩
      else none
    | _, _ => none
  | pow base expon =>
    match RatFn.ofExpr? (pow base expon) k with
    | some r => some ⟨RatFn.simplify r, one⟩
    | none =>
      if dependsOn base k then
        match expon with
        | const r =>
          match CplxConst.toRat? r with
          | some q =>
            if q.den != 1 then none
            else
              match factor base with
              | none => none
              | some t =>
                powTerm t q.num
          | none => none
        | _ => none
      else
        match splitAffine expon k with
        | none => none
        | some (a, b) =>
          let ratE := if b == zero then one else pow base b
          let geomE :=
            if a == zero then one
            else if a == one then base
            else pow base a
          match RatFn.ofExpr? ratE k with
          | some r => some ⟨RatFn.simplify r, simplify geomE⟩
          | none =>
            if dependsOn ratE k then none
            else some ⟨RatFn.ofPoly Poly.one, simplify geomE⟩
  | e =>
    match RatFn.ofExpr? e k with
    | some r => some ⟨RatFn.simplify r, one⟩
    | none =>
      if dependsOn e k then none
      else some ⟨RatFn.ofPoly Poly.one, one⟩

  powTerm (t : HypTerm) : Int → Option HypTerm
    | 0 => some ⟨RatFn.ofPoly Poly.one, one⟩
    | n =>
      if n > 0 then
        let n := n.toNat
        some ⟨
          RatFn.simplify ⟨Poly.powNat t.rat.num n, Poly.powNat t.rat.den n⟩,
          simplify (pow t.geom (ofNat n))⟩
      else
        -- t^{-m}
        if t.rat.num.isZero then none
        else
          let m := n.natAbs
          some ⟨
            RatFn.simplify ⟨Poly.powNat t.rat.den m, Poly.powNat t.rat.num m⟩,
            simplify (div one (pow t.geom (ofNat m)))⟩

/-- Gosper–Petkovšek form `P/Q = a/b · c(k+1)/c(k)`. -/
def gpFactor (P Q : Poly) : Poly × Poly × Poly :=
  let rec loop (a b c : Poly) (h fuel : Nat) : Poly × Poly × Poly :=
    match fuel with
    | 0 => (a, b, c)
    | fuel'+1 =>
      if h > gosperMaxShift then (a, b, c)
      else
        let g := Poly.gcd a (Poly.shift b (Int.ofNat h))
        if g.isOne || g.deg ≤ 0 then
          loop a b c (h + 1) fuel'
        else
          match Poly.exactDiv a g, Poly.exactDiv b (Poly.shift g (-Int.ofNat h)) with
          | some a', some b' =>
            let c' :=
              (List.range h).foldl
                (fun acc i => Poly.mul acc (Poly.shift g (-Int.ofNat (i + 1)))) c
            loop a' b' c' h fuel'
          | _, _ => loop a b c (h + 1) fuel'
  loop (Poly.strip P) (Poly.strip Q) Poly.one 1 (gosperMaxShift + 4)

def degNat (p : Poly) : Nat :=
  let d := p.deg
  if d ≤ 0 then 0 else d.toNat

/-- Predicted degree of the Gosper polynomial `x(k)`. -/
def gosperDeg (a b c : Poly) : Nat :=
  let da := a.deg
  let db := b.deg
  let dc := c.deg
  let toN (i : Int) : Nat := if i ≤ 0 then 0 else i.toNat
  let dNon := toN (dc - max da db)
  let cancel := da == db && Poly.lc a == Poly.lc b && da ≥ 0
  let dCan := if cancel then toN (dc - da + 1) else 0
  let dSpec :=
    if cancel && da > 0 then
      let dn := da.toNat
      let A1 := Poly.coeff a (dn - 1)
      let B1 := Poly.coeff b (dn - 1)
      let B1' := B1 - RatConst.ofInt da * Poly.lc b
      match RatConst.div (B1' - A1) (Poly.lc a) with
      | some q =>
        if q.den == 1 && q.num ≥ 0 then q.num.toNat else 0
      | none => 0
    else 0
  min gosperMaxDeg (max dNon (max dCan dSpec))

/-- RREF over ℚ of an augmented `m × (n+1)` matrix. Free unknowns → 0. -/
def solveRatAug (M0 : Array (Array RatConst)) (n : Nat) : Option (Array RatConst) :=
  let m := M0.size
  if n == 0 then some #[]
  else
    Id.run do
      let mut M := M0
      let mut pr : Nat := 0
      for col in [:n] do
        if pr >= m then break
        let mut piv := pr
        let mut found := false
        for r in [pr:m] do
          if r < M.size && col < M[r]!.size && !(M[r]![col]!).isZero then
            piv := r
            found := true
            break
        if !found then
          pure ()
        else
          if piv != pr then
            let tmp := M[pr]!
            M := M.set! pr M[piv]!
            M := M.set! piv tmp
          let pv := M[pr]![col]!
          match RatConst.inv pv with
          | none => pure ()
          | some inv =>
            M := M.set! pr (M[pr]!.map (fun x => x * inv))
            for r in [:m] do
              if r != pr then
                let f := M[r]![col]!
                if !f.isZero then
                  let mut row := M[r]!
                  for j in [:n + 1] do
                    row := row.set! j (row[j]! - f * M[pr]![j]!)
                  M := M.set! r row
            pr := pr + 1
      for r in [:m] do
        let mut allL := true
        for j in [:n] do
          if !(M[r]![j]!).isZero then allL := false
        if allL && n < M[r]!.size && !(M[r]![n]!).isZero then
          return none
      let mut x : Array RatConst := Array.replicate n RatConst.zero
      for r in [:m] do
        let mut pc : Option Nat := none
        for j in [:n] do
          if !(M[r]![j]!).isZero then
            pc := some j
            break
        match pc with
        | some j =>
          if n < M[r]!.size then
            x := x.set! j M[r]![n]!
        | none => pure ()
      pure (some x)

def solveRat (A : Array (Array RatConst)) (rhs : Array RatConst) : Option (Array RatConst) :=
  if A.size != rhs.size then none
  else if A.isEmpty then some #[]
  else
    let n := A[0]!.size
    let M :=
      Id.run do
        let mut out : Array (Array RatConst) := #[]
        for i in [:A.size] do
          out := out.push (A[i]!.push rhs[i]!)
        pure out
    solveRatAug M n

/-- Columns of `k^j` and `(k+1)^j` up to degree `d`. -/
def powTables (d : Nat) : Array Poly × Array Poly :=
  Id.run do
    let mut kp : Array Poly := Array.replicate (d + 1) Poly.one
    let mut k1p : Array Poly := Array.replicate (d + 1) Poly.one
    let Xp1 := Poly.add Poly.X Poly.one
    for j in [1:d + 1] do
      kp := kp.set! j (Poly.mul kp[j - 1]! Poly.X)
      k1p := k1p.set! j (Poly.mul k1p[j - 1]! Xp1)
    pure (kp, k1p)

def polyToExprCoeffs (cs : Array RatConst) (k : String) : Expr :=
  Id.run do
    let mut acc : Expr := zero
    for i in [:cs.size] do
      let c := cs[i]!
      if !c.isZero then
        let mon :=
          if i == 0 then ofRat c
          else if i == 1 then
            if c.isOne then var k else mul (ofRat c) (var k)
          else
            let pk := pow (var k) (ofNat i)
            if c.isOne then pk else mul (ofRat c) pk
        acc := if acc == zero then mon else add acc mon
    pure acc

def exprPoly (cs : Array Expr) (k : String) : Expr :=
  Id.run do
    let mut acc : Expr := zero
    for i in [:cs.size] do
      let c := simplify cs[i]!
      if c != zero then
        let mon :=
          if i == 0 then c
          else if i == 1 then
            if c == one then var k else mul c (var k)
          else
            let pk := pow (var k) (ofNat i)
            if c == one then pk else mul c pk
        acc := if acc == zero then mon else add acc mon
    pure (simplify acc)

def sigmaRat? (σ : Expr) : Option RatConst :=
  match simplify σ with
  | const r => CplxConst.toRat? r
  | e => if e == one then some RatConst.one else none

/-- Solve `a(k) x(k+1) − b(k−1) x(k) = c(k)` over ℚ. -/
def gosperPolyRat (a bPrev c : Poly) (k : String) : Option Expr :=
  let d := min gosperMaxDeg (gosperDeg a bPrev c)
  let (kp, k1p) := powTables d
  let n := d + 1
  let nRows := max (degNat c + 1) (d + max (degNat a) (degNat bPrev) + 2)
  Id.run do
    let mut AA : Array (Array RatConst) :=
      Array.replicate nRows (Array.replicate n RatConst.zero)
    let mut bb : Array RatConst := Array.replicate nRows RatConst.zero
    for i in [:nRows] do
      bb := bb.set! i (Poly.coeff c i)
    for j in [:n] do
      let W := Poly.sub (Poly.mul a k1p[j]!) (Poly.mul bPrev kp[j]!)
      for i in [:nRows] do
        AA := AA.set! i (AA[i]!.set! j (Poly.coeff W i))
    match solveRat AA bb with
    | none => pure none
    | some cs =>
      if cs.all (·.isZero) && !c.isZero then pure none
      else pure (some (polyToExprCoeffs cs k))

/-- Same equation with a symbolic constant `σ` in front of `a`. -/
def gosperPolyExpr (a bPrev c : Poly) (σ : Expr) (k : String) : Option Expr :=
  let d := min gosperMaxDeg (max 4 (degNat c + 2))
  let (kp, k1p) := powTables d
  let n := d + 1
  let nRows := max (degNat c + 1) (d + max (degNat a) (degNat bPrev) + 2)
  Id.run do
    let mut rows : Array (Array Expr) := Array.replicate nRows (Array.replicate n zero)
    let mut bcol : Array (Array Expr) := Array.replicate nRows #[zero]
    for i in [:nRows] do
      bcol := bcol.set! i #[ofRat (Poly.coeff c i)]
    for j in [:n] do
      let U := Poly.mul a k1p[j]!
      let V := Poly.mul bPrev kp[j]!
      for i in [:nRows] do
        let cij := simplify (sub (mul σ (ofRat (Poly.coeff U i))) (ofRat (Poly.coeff V i)))
        rows := rows.set! i (rows[i]!.set! j cij)
    match Mat.solve rows bcol with
    | .unique x =>
      let cs := x.map fun (row : Array Expr) =>
        if row.size > 0 then row[0]! else zero
      pure (some (exprPoly cs k))
    | .general x nf =>
      let mut cs : Array Expr := x.map fun (row : Array Expr) =>
        if row.size > 0 then row[0]! else zero
      for i in [:nf] do
        cs := cs.map fun e => subst e (Mat.freeParamName i) zero
      pure (some (exprPoly cs k))
    | _ => pure none

/-- Solve `σ a(k) x(k+1) − b(k−1) x(k) = c(k)` for polynomial `x`. -/
def gosperPolyσ (a bPrev c : Poly) (σ : Expr) (k : String) : Option Expr :=
  match sigmaRat? σ with
  | some σr =>
    if σr.isZero then none
    else
      let a := if σr.isOne then a else Poly.scale σr a
      gosperPolyRat a bPrev c k
  | none => gosperPolyExpr a bPrev c σ k

/-- Antidifference `s` with `s(k+1) − s(k) = t(k)`, if Gosper finds one. -/
def gosperAntidiff (t : Expr) (k : String) : Option Expr :=
  match asHypTerm? t k with
  | none => none
  | some ht =>
    if ht.rat.num.isZero then some zero
    else if ht.rat.den.isZero then none
    else
      let num := ht.rat.num
      let den := ht.rat.den
      -- r_rat(k) = rat(k+1)/rat(k)
      let P := Poly.mul (Poly.shift num 1) den
      let Q := Poly.mul (Poly.shift den 1) num
      if Q.isZero then none
      else
        let r := RatFn.simplify ⟨P, Q⟩
        if r.den.isZero then none
        else
          let (a, b, c) := gpFactor r.num r.den
          if a.isZero then none
          else
            let bPrev := Poly.shift b (-1)
            let σ := simplify ht.geom
            match gosperPolyσ a bPrev c σ k with
            | none => none
            | some xE =>
              -- z = b(k−1) x / c ;  s = z · t
              let bE :=
                if bPrev.isOne then one
                else if bPrev.isZero then zero
                else Poly.toExpr bPrev k
              let cE :=
                if c.isOne then one
                else Poly.toExpr c k
              let z :=
                if c.isOne then mul bE xE
                else div (mul bE xE) cE
              some (simplify (mul z t))

/-- Check `s(k+1) − s(k) = t(k)` at a few integer points when evaluable. -/
def gosperVerify (s t : Expr) (k : String) : Bool :=
  let pts : List Int := [2, 3, 4, 5, 6]
  Id.run do
    for n in pts do
      let Δ := sub (subst s k (ofInt (n + 1))) (subst s k (ofInt n))
      let want := subst t k (ofInt n)
      match eval? (simplify (sub Δ want)) with
      | some c =>
        if !c.isZero then return false
      | none => pure ()
    pure true

/--
  Closed form for `∑_{k=lo}^{hi} t(k)` via Gosper, if `t` is a
  hypergeometric term with a polynomial Gosper certificate.
-/
def gosperSum (t : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  match gosperAntidiff t k with
  | none => none
  | some s =>
    if !gosperVerify s t k then none
    else
      let sHi := subst s k (simplify (add hi one))
      let sLo := subst s k (simplify lo)
      let out := simplify (sub sHi sLo)
      if dependsOn out k then none
      else some (simplify (Expr.normalForm out k))

end Taschenrechner
