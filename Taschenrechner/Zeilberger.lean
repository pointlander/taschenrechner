/-
  Zeilberger / Sister Celine: creative telescoping for hypergeometric
  terms F(n,k) in a discrete parameter `n`.

  Finds k-free coefficients a_{i,j}(n) with
    ∑_{i,j} a_{i,j} F(n+i, k+j) = 0,
  then sums over k to a linear recurrence for f(n) = ∑_k F(n,k).
  Caps on I, J, and degree keep compile-time `#guard`s bounded.

  References: Petkovšek–Wilf–Zeilberger, *A = B*; Celine (1920s).
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Normal
import Taschenrechner.Solve
import Taschenrechner.LinAlg
import Taschenrechner.Eval

namespace Taschenrechner

open Expr

def zeilIMax : Nat := 2
def zeilJMax : Nat := 2
def zeilMaxDeg : Nat := 10
def zeilMaxFactShift : Nat := 8

/-! ### Polynomials in `k` with expression coefficients (ℚ(n)[k]) -/

structure EPoly where
  coeffs : Array Expr
  deriving Repr, Inhabited

namespace EPoly

def zero : EPoly := ⟨#[]⟩

def strip (p : EPoly) : EPoly :=
  Id.run do
    let mut cs := p.coeffs
    while cs.size > 0 && isZeroExpr cs.back! do
      cs := cs.pop
    pure ⟨cs⟩

def deg (p : EPoly) : Int :=
  let p := strip p
  if p.coeffs.isEmpty then -1 else (p.coeffs.size : Int) - 1

def isZero (p : EPoly) : Bool := strip p |>.coeffs.isEmpty

def coeff (p : EPoly) (i : Nat) : Expr :=
  p.coeffs[i]?.getD Expr.zero

def ofConst (e : Expr) : EPoly :=
  let e := simplify e
  if isZeroExpr e then zero else ⟨#[e]⟩

def X : EPoly := ⟨#[Expr.zero, Expr.one]⟩

def add (a b : EPoly) : EPoly :=
  Id.run do
    let n := max a.coeffs.size b.coeffs.size
    let mut cs : Array Expr := Array.replicate n Expr.zero
    for i in [:n] do
      cs := cs.set! i (simplify (Expr.add (coeff a i) (coeff b i)))
    pure (strip ⟨cs⟩)

def neg (p : EPoly) : EPoly :=
  strip ⟨p.coeffs.map fun c => simplify (Expr.neg c)⟩

def scale (s : Expr) (p : EPoly) : EPoly :=
  let s := simplify s
  if isZeroExpr s then zero
  else strip ⟨p.coeffs.map fun c => simplify (mul s c)⟩

def mul (a b : EPoly) : EPoly :=
  if a.isZero || b.isZero then zero
  else
    Id.run do
      let n := a.coeffs.size + b.coeffs.size - 1
      let mut cs : Array Expr := Array.replicate n Expr.zero
      for i in [:a.coeffs.size] do
        for j in [:b.coeffs.size] do
          let t := simplify (Expr.mul a.coeffs[i]! b.coeffs[j]!)
          let idx := i + j
          cs := cs.set! idx (simplify (Expr.add cs[idx]! t))
      pure (strip ⟨cs⟩)

def powNat : EPoly → Nat → EPoly
  | _, 0 => ofConst one
  | p, n+1 =>
    Id.run do
      let mut acc := p
      for _ in [:n] do
        acc := mul acc p
      pure acc

/-- Parse a polynomial in `k` (coefficients may involve other symbols). -/
partial def ofExpr? (e : Expr) (k : String) : Option EPoly :=
  go (simplify e)
where
  go : Expr → Option EPoly
  | Expr.const c => some (ofConst (Expr.const c))
  | Expr.var v =>
    if v == k then some X else some (ofConst (Expr.var v))
  | Expr.add a b =>
    match go a, go b with
    | some pa, some pb => some (add pa pb)
    | _, _ => none
  | Expr.mul a b =>
    match go a, go b with
    | some pa, some pb =>
      if deg pa + deg pb > Int.ofNat zeilMaxDeg then none
      else some (mul pa pb)
    | _, _ => none
  | Expr.pow base expn =>
    match asNat? (simplify expn) with
    | some m =>
      if m > zeilMaxDeg then none
      else
        match go base with
        | some p =>
          if deg p * Int.ofNat m > Int.ofNat zeilMaxDeg then none
          else some (powNat p m)
        | none => none
    | none =>
      if dependsOn (Expr.pow base expn) k then none
      else some (ofConst (Expr.pow base expn))
  | Expr.factorial e =>
    if dependsOn e k then none else some (ofConst (Expr.factorial e))
  | Expr.gamma e =>
    if dependsOn e k then none else some (ofConst (Expr.gamma e))
  | Expr.sin e => if dependsOn e k then none else some (ofConst (Expr.sin e))
  | Expr.cos e => if dependsOn e k then none else some (ofConst (Expr.cos e))
  | Expr.exp e => if dependsOn e k then none else some (ofConst (Expr.exp e))
  | Expr.ln e => if dependsOn e k then none else some (ofConst (Expr.ln e))
  | e =>
    if dependsOn e k then none else some (ofConst e)

def toExpr (p : EPoly) (k : String) : Expr :=
  Id.run do
    let mut acc : Expr := Expr.zero
    for i in [:p.coeffs.size] do
      let c := p.coeffs[i]!
      if !isZeroExpr c then
        let mon :=
          if i == 0 then c
          else if i == 1 then
            if c == Expr.one then Expr.var k else Expr.mul c (Expr.var k)
          else
            let pk := Expr.pow (Expr.var k) (ofNat i)
            if c == Expr.one then pk else Expr.mul c pk
        acc := if acc == Expr.zero then mon else Expr.add acc mon
    pure (simplify acc)

end EPoly

structure ERat where
  num : EPoly
  den : EPoly
  deriving Repr, Inhabited

namespace ERat

def ofPoly (p : EPoly) : ERat := ⟨p, EPoly.ofConst one⟩

def add (a b : ERat) : ERat :=
  ⟨EPoly.add (EPoly.mul a.num b.den) (EPoly.mul b.num a.den),
   EPoly.mul a.den b.den⟩

def mul (a b : ERat) : ERat :=
  ⟨EPoly.mul a.num b.num, EPoly.mul a.den b.den⟩

def scale (s : Expr) (r : ERat) : ERat :=
  ⟨EPoly.scale s r.num, r.den⟩

partial def ofExpr? (e : Expr) (k : String) : Option ERat :=
  go (simplify e)
where
  go : Expr → Option ERat
  | Expr.mul a (Expr.pow b (Expr.const r)) =>
    match CplxConst.toRat? r with
    | some q =>
      if q == RatConst.negOne then
        match go a, EPoly.ofExpr? b k with
        | some ra, some db => some ⟨ra.num, EPoly.mul ra.den db⟩
        | _, _ => none
      else
        match EPoly.ofExpr? (Expr.mul a (Expr.pow b (Expr.const r))) k with
        | some p => some (ofPoly p)
        | none => none
    | none =>
      match EPoly.ofExpr? (Expr.mul a (Expr.pow b (Expr.const r))) k with
      | some p => some (ofPoly p)
      | none => none
  | Expr.add a b =>
    match go a, go b with
    | some ra, some rb => some (add ra rb)
    | _, _ => none
  | Expr.mul a b =>
    match go a, go b with
    | some ra, some rb => some (mul ra rb)
    | _, _ => none
  | Expr.pow base (Expr.const r) =>
    match CplxConst.toRat? r with
    | some q =>
      if q == RatConst.negOne then
        match EPoly.ofExpr? base k with
        | some d => some ⟨EPoly.ofConst Expr.one, d⟩
        | none => none
      else
        match EPoly.ofExpr? (Expr.pow base (Expr.const r)) k with
        | some p => some (ofPoly p)
        | none => none
    | none =>
      match EPoly.ofExpr? (Expr.pow base (Expr.const r)) k with
      | some p => some (ofPoly p)
      | none => none
  | e =>
    match EPoly.ofExpr? e k with
    | some p => some (ofPoly p)
    | none => none

end ERat

/-! ### Factorial ratio cancellation -/

/-- `a − b` as an integer, if it is one. -/
def exprIntDiff? (a b : Expr) : Option Int :=
  let d := simplify (expand (sub a b))
  match d with
  | const c =>
    match CplxConst.toRat? c with
    | some q => if q.den == 1 then some q.num else none
    | none => none
  | _ =>
    Id.run do
      for i in [:zeilMaxFactShift * 2 + 1] do
        let m : Int := Int.ofNat i - Int.ofNat zeilMaxFactShift
        if isZeroExpr (sub d (ofInt m)) then return some m
      none

/-- `(u+1)⋯(u+m)`. -/
def risingFact (u : Expr) (m : Nat) : Expr :=
  (List.range m).foldl (fun acc i => mul acc (add u (ofNat (i + 1)))) one

/-- `num! / den!` when `num − den` is a small integer. -/
def factQuotient? (numArg denArg : Expr) : Option Expr :=
  match exprIntDiff? numArg denArg with
  | none => none
  | some m =>
    if m.natAbs > zeilMaxFactShift then none
    else if m == 0 then some one
    else if m > 0 then some (simplify (risingFact denArg m.toNat))
    else
      -- den = num + |m|
      some (simplify (div one (risingFact numArg m.natAbs)))

/-- Repeat list `xs` `m` times. -/
def repList (m : Nat) (xs : List Expr) : List Expr :=
  (List.range m).foldl (fun acc _ => acc ++ xs) []

/-- Split `e` into numerator / denominator factors. -/
partial def fracFactors : Expr → List Expr × List Expr
  | mul a b =>
    let (n1, d1) := fracFactors a
    let (n2, d2) := fracFactors b
    (n1 ++ n2, d1 ++ d2)
  | pow a (const r) =>
    match CplxConst.toRat? r with
    | some q =>
      if q.den != 1 then ([pow a (const r)], [])
      else if q.num == 0 then ([one], [])
      else
        let (n, d) := fracFactors a
        if q.num > 0 then (repList q.num.toNat n, repList q.num.toNat d)
        else
          let m := q.num.natAbs
          -- (n/d)^{−m} = d^m / n^m
          (repList m d, repList m n)
    | none => ([pow a (const r)], [])
  | e => ([e], [])

/-- `base^e` as a pair; a bare factor is `base^1`. -/
def asPowPair : Expr → Expr × Expr
  | pow b e => (b, e)
  | e => (e, one)

/-- Combine equal bases: `x^{k+1}/x^k → x`. -/
def reducePowRatio (e : Expr) : Expr :=
  let (ns, ds) := fracFactors e
  Id.run do
    let mut bases : Array Expr := Array.empty
    let mut exps : Array Expr := Array.empty
    for f in ns do
      let (b0, e0) := asPowPair f
      let b := simplify b0
      let mut found := false
      for i in [:bases.size] do
        if !found && isZeroExpr (sub bases[i]! b) then
          exps := exps.set! i (simplify (add exps[i]! e0))
          found := true
      if !found then
        bases := bases.push b
        exps := exps.push (simplify e0)
    for f in ds do
      let (b0, e0) := asPowPair f
      let b := simplify b0
      let mut found := false
      for i in [:bases.size] do
        if !found && isZeroExpr (sub bases[i]! b) then
          exps := exps.set! i (simplify (sub exps[i]! e0))
          found := true
      if !found then
        bases := bases.push b
        exps := exps.push (simplify (neg e0))
    let mut acc : Expr := one
    for i in [:bases.size] do
      let e := exps[i]!
      if isZeroExpr e then
        pure ()
      else if e == one then
        acc := mul acc bases[i]!
      else
        acc := mul acc (pow bases[i]! e)
    simplify acc

/-- Cancel matching factorials whose arguments differ by an integer. -/
def reduceFactRatio (e : Expr) : Expr :=
  let e := simplify e
  let (nums, dens) := fracFactors e
  Id.run do
    let mut ns : Array Expr := nums.toArray
    let mut ds : Array Expr := dens.toArray
    let mut extra : Expr := one
    let mut changed := true
    let mut steps : Nat := 0
    while changed && steps < 32 do
      changed := false
      steps := steps + 1
      -- Prefer smallest |arg difference| so (n−k)! pairs with (n−k−1)!, not (n−k+2)!
      let mut best : Option (Nat × Nat × Expr × Nat) := none
      for i in [:ns.size] do
        match ns[i]! with
        | factorial u =>
          for j in [:ds.size] do
            match ds[j]! with
            | factorial v =>
              match exprIntDiff? u v with
              | some m =>
                if m.natAbs ≤ zeilMaxFactShift then
                  let better :=
                    match best with
                    | none => true
                    | some (_, _, _, b) => m.natAbs < b
                  if better then
                    match factQuotient? u v with
                    | some q => best := some (i, j, q, m.natAbs)
                    | none => pure ()
              | none => pure ()
            | _ => pure ()
        | _ => pure ()
      match best with
      | some (i, j, q, _) =>
        ns := ns.eraseIdx! i
        ds := ds.eraseIdx! j
        extra := mul extra q
        changed := true
      | none => pure ()
    let mut acc : Expr := extra
    for f in ns do
      acc := mul acc f
    for f in ds do
      acc := mul acc (div one f)
    simplify acc

/-- Expand arguments of factorials so `n−(k+1)` becomes `n−k−1`. -/
partial def expandFactArgs : Expr → Expr
  | factorial a => factorial (expand a)
  | mul a b => mul (expandFactArgs a) (expandFactArgs b)
  | add a b => add (expandFactArgs a) (expandFactArgs b)
  | pow a b => pow (expandFactArgs a) (expandFactArgs b)
  | e => e

/-- `F(n+di, k+dj) / F(n, k)` reduced to a rational in `k`, if possible. -/
def hypShiftRatio (F : Expr) (n k : String) (di dj : Int) : Option ERat :=
  let Fn :=
    if di == 0 then F
    else subst F n (add (var n) (ofInt di))
  let Fsh :=
    if dj == 0 then Fn
    else subst Fn k (add (var k) (ofInt dj))
  let F0 := expandFactArgs (simplify F)
  let F1 := expandFactArgs (simplify Fsh)
  let ratio := reducePowRatio (reduceFactRatio (simplify (div F1 F0)))
  let stillFact : Bool :=
    Id.run do
      let (ns, ds) := fracFactors ratio
      for f in ns ++ ds do
        match f with
        | factorial _ => return true
        | _ => pure ()
      false
  if stillFact then none
  else ERat.ofExpr? ratio k

/-! ### Sister Celine -/

/-- Linear recurrence coefficients `b_i(n)` for `∑_i b_i f(n+i) = 0`. -/
def celineRec? (F : Expr) (n k : String) (I J : Nat) : Option (Array Expr) :=
  let nU := (I + 1) * (J + 1)
  if nU == 0 then none
  else
    Id.run do
      let mut rats : Array (Option ERat) := Array.replicate nU none
      for i in [:I + 1] do
        for j in [:J + 1] do
          let idx := i * (J + 1) + j
          rats := rats.set! idx (hypShiftRatio F n k (Int.ofNat i) (Int.ofNat j))
      for i in [:nU] do
        if rats[i]!.isNone then return none
      -- piece_i = ρ.num · ∏_{ℓ≠i} ρ.den  (polynomial in k; column i of the system)
      let mut pieces : Array EPoly := Array.replicate nU EPoly.zero
      let mut maxD : Nat := 0
      for i in [:nU] do
        match rats[i]! with
        | some r =>
          let mut restD : EPoly := EPoly.ofConst one
          for ℓ in [:nU] do
            if ℓ != i then
              match rats[ℓ]! with
              | some rℓ => restD := EPoly.mul restD rℓ.den
              | none => pure ()
          let piece := EPoly.mul r.num restD
          pieces := pieces.set! i piece
          let di := (EPoly.strip piece).coeffs.size
          if di > maxD then maxD := di
        | none => pure ()
      if maxD == 0 then return none
      -- equate coeffs of k^m to 0: row m, column i is [k^m] piece_i
      let mut rowsA : Array (Array Expr) := Array.empty
      let mut rowsB : Array (Array Expr) := Array.empty
      for m in [:maxD] do
        let mut row : Array Expr := Array.empty
        let mut any := false
        for i in [:nU] do
          let c := simplify (EPoly.coeff pieces[i]! m)
          if !isZeroExpr c then any := true
          row := row.push c
        if any then
          rowsA := rowsA.push row
          rowsB := rowsB.push #[zero]
      if rowsA.isEmpty then return none
      for row in rowsA do
        for c in row do
          if dependsOn c k then return none
      match Mat.solve rowsA rowsB with
      | .general x _nf =>
        -- set t1=1, other free params 0
        let mut sol := x
        for p in [:_nf] do
          let t := Mat.freeParamName p
          let val := if p == 0 then one else zero
          sol := Mat.map sol (fun e => subst e t val)
        let mut allZ := true
        for i in [:nU] do
          if !isZeroExpr (Mat.get! sol i 0) then allZ := false
        if allZ then none
        else
          -- b_i = ∑_j a_{i,j}
          let mut bs : Array Expr := Array.replicate (I + 1) zero
          for i in [:I + 1] do
            let mut acc : Expr := zero
            for j in [:J + 1] do
              let aij := simplify (Mat.get! sol (i * (J + 1) + j) 0)
              acc := add acc aij
            bs := bs.set! i (simplify acc)
          -- drop overall zero recurrence
          let mut anyB := false
          for i in [:I + 1] do
            if !isZeroExpr bs[i]! then anyB := true
          if anyB then some bs else none
      | .unique x =>
        let mut allZ := true
        for i in [:nU] do
          if !isZeroExpr (Mat.get! x i 0) then allZ := false
        if allZ then none
        else
          let mut bs : Array Expr := Array.replicate (I + 1) zero
          for i in [:I + 1] do
            let mut acc : Expr := zero
            for j in [:J + 1] do
              let aij := simplify (Mat.get! x (i * (J + 1) + j) 0)
              acc := add acc aij
            bs := bs.set! i (simplify acc)
          some bs
      | _ => none

/-- Search small (I,J) for a Celine recurrence. -/
def zeilbergerOp? (F : Expr) (n k : String) : Option (Array Expr) :=
  let pairs : List (Nat × Nat) := [(1, 1), (1, 0)]
  Id.run do
    for (I, J) in pairs do
      if I ≤ zeilIMax && J ≤ zeilJMax then
        match celineRec? F n k I J with
        | some bs => return some bs
        | none => pure ()
    none

/--
  Binomial theorem: `F = C(n,k) q^k` iff
  `F(n,k+1)/F = q (n−k)/(k+1)` with `q` free of `k`.
  Then `∑_k F = (1+q)^n` on `k = 0…n`.
-/
def eratEq (a b : ERat) : Bool :=
  let d := EPoly.add (EPoly.mul a.num b.den) (EPoly.neg (EPoly.mul b.num a.den))
  (EPoly.strip d).coeffs.all fun c =>
    let c := simplify c
    c == zero || match c with | const q => q.isZero | _ => false

/-- Constant `q` such that `num = q · den` as polynomials in `k`. -/
def epolyRatioConst (num den : EPoly) : Option Expr :=
  let d := max num.coeffs.size den.coeffs.size
  -- Cross-multiply: n_i d_j − n_j d_i = 0 for all i, j
  Id.run do
    for i in [:d] do
      for j in [:d] do
        let c := simplify (expand (sub
          (mul (EPoly.coeff num i) (EPoly.coeff den j))
          (mul (EPoly.coeff num j) (EPoly.coeff den i))))
        let z := c == zero || match c with | const q => q.isZero | _ => false
        if !z then return none
    for i in [:d] do
      let di := simplify (EPoly.coeff den i)
      if !(di == zero || match di with | const q => q.isZero | _ => false) then
        let q := simplify (div (EPoly.coeff num i) di)
        if dependsOn q "k" then return none
        else return some q
    none

def binomTheorem? (F : Expr) (n k : String) : Option Expr :=
  match hypShiftRatio F n k 0 1, hypShiftRatio F n k 1 0 with
  | some r01, some r10 =>
    match ERat.ofExpr? (div (add (var n) one) (add (sub (var n) (var k)) one)) k,
          ERat.ofExpr? (div (sub (var n) (var k)) (add (var k) one)) k with
    | some w10, some w01 =>
      if !eratEq r10 w10 then none
      else
        let qNum := EPoly.mul r01.num w01.den
        let qDen := EPoly.mul r01.den w01.num
        match epolyRatioConst qNum qDen with
        | some q => some (pow (add one q) (var n))
        | none => none
    | _, _ => none
  | _, _ => none

end Taschenrechner
