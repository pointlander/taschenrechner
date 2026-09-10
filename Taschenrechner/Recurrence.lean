/-
  Linear recurrences (`rsolve`).

  * Constant-coefficient `Σ a_k y(n+k) = g(n)` via the characteristic
    polynomial (real `r^n` / `n^j r^n`; conjugate pairs `ρ^n cos/sin`)
  * Polynomial and geometric `q^n` forcing by undetermined coefficients
  * ICs `y(0), y(1), …`
  * First-order variable-coeff `y(n+1)=a(n) y(n)+b(n)` via `product` / `sum`
  * Systems `Y(n+1) = A Y(n)` via Jordan `A^n`; `Y(n+1)=A Y(n)+g` via
    `Yp=(I−A)⁻¹g` or discrete variation of parameters
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Normal
import Taschenrechner.Solve
import Taschenrechner.Poly
import Taschenrechner.ODE
import Taschenrechner.Matrix
import Taschenrechner.Eigen
import Taschenrechner.Eval
import Taschenrechner.Sum
import Taschenrechner.Zeilberger

namespace Taschenrechner

open Expr

def maxSeqShift : Nat := 6

/-- `y(n+k)` stored as the variable `y[n+k]`. -/
def mkSeqVar (y idx : String) (shift : Int) : String :=
  if shift == 0 then s!"{y}[{idx}]"
  else if shift > 0 then s!"{y}[{idx}+{shift}]"
  else s!"{y}[{idx}-{shift.natAbs}]"

def parseSeqVar? (name : String) : Option (String × String × Int) :=
  match name.splitOn "[" with
  | [y, rest] =>
    if y.isEmpty || !rest.endsWith "]" then none
    else
      let inner := String.ofList (rest.toList.dropLast)
      if inner.isEmpty then none
      else if inner.contains '+' then
        match inner.splitOn "+" with
        | [idx, ks] =>
          match ks.toInt? with
          | some k => some (y, idx, k)
          | none => none
        | _ => none
      else if inner.contains '-' then
        match inner.splitOn "-" with
        | [idx, ks] =>
          if idx.isEmpty then none
          else
            match ks.toInt? with
            | some k => some (y, idx, -k)
            | none => none
        | _ => none
      else some (y, inner, 0)
  | _ => none

/-- `n` or `n+k` / `k+n` / `n-k` with integer `k`. -/
def asAffineIndex? (e : Expr) : Option (String × Int) :=
  let asInt? : Expr → Option Int
    | const c =>
      match CplxConst.toRat? c with
      | some q => if q.den == 1 then some q.num else none
      | none => none
    | _ => none
  match simplify e with
  | var v => some (v, 0)
  | add a b =>
    match a, b with
    | var v, t => (asInt? t).map fun k => (v, k)
    | t, var v => (asInt? t).map fun k => (v, k)
    | _, _ => none
  | _ => none

def seqTerm (y idx : String) (shift : Int) : Expr :=
  var (mkSeqVar y idx shift)

/-- Integer constant, if any. -/
def asPlainInt? (e : Expr) : Option Int :=
  match simplify e with
  | const c =>
    match CplxConst.toRat? c with
    | some q => if q.den == 1 then some q.num else none
    | none => none
  | _ => none

/-- Collect every `y(n+k)` occurring in `e`. -/
partial def collectSeqVars : Expr → List (String × String × Int)
  | var name =>
    match parseSeqVar? name with
    | some t => [t]
    | none => []
  | add a b | mul a b | pow a b | eq a b | lt a b | le a b =>
    collectSeqVars a ++ collectSeqVars b
  | Expr.ite c t e => collectSeqVars c ++ collectSeqVars t ++ collectSeqVars e
  | sin a | cos a | tan a | sinh a | cosh a | tanh a
  | exp a | ln a | atan a | asin a | acos a | sec a | csc a | cot a
  | factorial a | gamma a | floor a | abs a | re a | im a | conj a =>
    collectSeqVars a
  | mat rows =>
    rows.foldl (fun acc row =>
      row.foldl (fun acc e => acc ++ collectSeqVars e) acc) []
  | const _ => []

def inferSeqNames? (e : Expr) : Option (String × String) :=
  let ts := collectSeqVars e
  match ts with
  | [] => none
  | (y, n, _) :: rest =>
    if rest.all (fun t => t.1 == y && t.2.1 == n) then some (y, n) else none

/--
  Linear form `Σ c_k y(n+k) + D = 0` with shifts in `[-maxSeqShift, maxSeqShift]`.
  `cs[i]` is the coefficient of `y(n + (i − maxSeqShift))`.
-/
partial def linearFormInSeq (e : Expr) (y idx : String) : Option (Array Expr × Expr) :=
  go (simplify e)
where
  z : Array Expr := Array.replicate (2 * maxSeqShift + 1) zero
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
    match parseSeqVar? name with
    | some (y', n', k) =>
      if y' != y || n' != idx then none
      else if k.natAbs > maxSeqShift then none
      else
        let i := (k + Int.ofNat maxSeqShift).toNat
        some (z.set! i one, zero)
    | none =>
      if name == y then none
      else some (z, var name)
  | const c => some (z, const c)
  | e =>
    if collectSeqVars e |>.any (fun t => t.1 == y) then
      match e with
      | mul a b =>
        let aS := collectSeqVars a |>.any (fun t => t.1 == y)
        let bS := collectSeqVars b |>.any (fun t => t.1 == y)
        if aS && !bS then
          match go a with
          | some (cs, dd) =>
            if dd == zero then
              some (cs.map (fun u => simplify (mul u b)), zero)
            else none
          | none => none
        else if bS && !aS then
          match go b with
          | some (cs, dd) =>
            if dd == zero then
              some (cs.map (fun u => simplify (mul u a)), zero)
            else none
          | none => none
        else none
      | _ => none
    else
      some (z, e)

/-- Slice to the support of nonzero coefficients (lowest unknown is `y(n)`). -/
def sliceNonzeroCoeffs (cs : Array Expr) : Option (Array Expr) :=
  Id.run do
    let mut lo : Option Nat := none
    let mut hi : Nat := 0
    for i in [:cs.size] do
      if !(isZeroExpr cs[i]!) then
        hi := i
        if lo.isNone then lo := some i
    match lo with
    | none => none
    | some lo0 =>
      let mut out : Array Expr := Array.empty
      for i in [lo0:hi + 1] do
        out := out.push (simplify cs[i]!)
      some out

/-- Normalize so the lowest unknown is `y(n)` (`as[0]`), rational coefficients. -/
def normalizeSeqCoeffs (cs : Array Expr) : Option (Array RatConst) :=
  match sliceNonzeroCoeffs cs with
  | none => none
  | some as => ratCoeffArray? as

/-- `r^n`, with `1^n → 1` and `0^n` left as a power. -/
def recPowN (r : Expr) (idx : String) : Expr :=
  let r := simplify r
  if r == one then one
  else if r == zero then pow zero (var idx)
  else pow r (var idx)

/-- `1, n, …, n^{m-1}` times `r^n`. -/
def recRealBasis (r : Expr) (m : Nat) (idx : String) : List Expr :=
  let nv := var idx
  let rn := recPowN r idx
  (List.range m).map fun k =>
    let nk := if k == 0 then one else pow nv (ofNat k)
    simplify (mul nk rn)

/-- Polar `(ρ, θ)` for `a + b i` with rational `a, b`. -/
def recPolar? (a b : RatConst) : Option (Expr × Expr) :=
  if b.isZero then none
  else if a.isZero then
    let rho := ofRat b.abs
    let th :=
      if b.num ≥ 0 then div piE (ofInt 2)
      else neg (div piE (ofInt 2))
    some (rho, th)
  else
    let rho := sqrt (ofRat (a * a + b * b))
    let th :=
      let ath := atan (ofRat (match RatConst.div b a with | some q => q | none => b))
      if a.num ≥ 0 then ath else add ath piE
    some (simplify rho, simplify th)

/-- `n^k ρ^n cos(n θ)` and `sin`, `k = 0…m-1`. -/
def recTrigBasis (rho theta : Expr) (m : Nat) (idx : String) : List Expr :=
  let nv := var idx
  let rn := recPowN rho idx
  let arg := mul nv theta
  let c0 := simplify (mul rn (cos arg))
  let s0 := simplify (mul rn (sin arg))
  (List.range m).foldl (fun acc k =>
    let nk := if k == 0 then one else pow nv (ofNat k)
    acc ++ [simplify (mul nk c0), simplify (mul nk s0)]) []

/-- Real fundamental solutions of a characteristic polynomial. -/
def recBasis (roots : List (Expr × Nat)) (idx : String) : List Expr :=
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
            basis := basis ++ recRealBasis (ofRat a) m idx
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
                    match recPolar? a (if b.num < 0 then RatConst.neg b else b) with
                    | some (rho, th) =>
                      basis := basis ++ recTrigBasis rho th m idx
                    | none =>
                      basis := basis ++ recRealBasis r m idx
                      basis := basis ++ recRealBasis r2 m idx
                    found := true
                | none => pure ()
            if !found then
              used := used.set! i true
              basis := basis ++ recRealBasis r m idx
        | none =>
          used := used.set! i true
          basis := basis ++ recRealBasis r m idx
    pure basis

/-- Homogeneous solution: `C·u` (order 1) or `Σ Cᵢ uᵢ`. -/
def recCombo (us : List Expr) : Expr :=
  if us.length == 1 then simplify (mul odeC us[0]!)
  else linearComboBasis us

/-- `Σ a_k f(n+k)`. -/
def applyRecOp (as : Array RatConst) (f : Expr) (idx : String) : Expr :=
  Id.run do
    let mut acc : Expr := zero
    for k in [:as.size] do
      if !(as[k]!.isZero) then
        let fk := subst f idx (add (var idx) (ofNat k))
        acc := add acc (mul (ofRat as[k]!) fk)
    simplify acc

/-- `L[n^s q^n] / q^n = Σ a_k (n+k)^s q^k`. -/
def recApplyOnGeom (as : Array RatConst) (s : Nat) (q : Expr) (idx : String) : Expr :=
  Id.run do
    let mut acc : Expr := zero
    for k in [:as.size] do
      if !(as[k]!.isZero) then
        let nks :=
          if s == 0 then one
          else pow (add (var idx) (ofNat k)) (ofNat s)
        let qk := if k == 0 then one else pow q (ofNat k)
        acc := add acc (mul (ofRat as[k]!) (mul nks qk))
    simplify acc

/-- Multiplicity of characteristic root `q` (0 if not a root). -/
partial def recRootMult (as : Array RatConst) (q : Expr) : Nat :=
  let rec go (s fuel : Nat) : Nat :=
    match fuel with
    | 0 => s
    | fuel' + 1 =>
      let K := recApplyOnGeom as s q "n"
      if K == zero || isZeroExpr K "n" then go (s + 1) fuel' else s
  go 0 (as.size + 1)

/-- Undetermined coefficients for a polynomial RHS. -/
def recParticularPoly (as : Array RatConst) (g : Expr) (idx : String) : Option Expr :=
  match asPolynomialIn? (simplify (Expr.cancel g)) idx with
  | none => none
  | some p =>
    if Poly.isZero p then some zero
    else
      let s := recRootMult as one
      let deg := (Poly.strip p).deg.toNat
      let nA := deg + 1
      let names : Array String :=
        Id.run do
          let mut ns : Array String := Array.empty
          for i in [:nA] do
            ns := ns.push s!"__ucR{i}"
          pure ns
      let nv := var idx
      let body : Expr :=
        Id.run do
          let mut acc : Expr := zero
          for i in [:nA] do
            let nk := if i == 0 then one else pow nv (ofNat i)
            acc := add acc (mul (var names[i]!) nk)
          pure acc
      let yp0 := if s == 0 then body else mul (pow nv (ofNat s)) body
      let residual := simplify (sub (applyRecOp as yp0 idx) g)
      match affineForm residual names.toList with
      | none => none
      | some (cA, k) =>
        let cPolys : Option (Array Poly) :=
          Id.run do
            let mut ps : Array Poly := Array.empty
            for i in [:nA] do
              match asPolynomialIn? cA[i]! idx with
              | none => return none
              | some pi => ps := ps.push pi
            some ps
        match cPolys, asPolynomialIn? k idx with
        | some cps, some kp =>
          Id.run do
            let mut maxD : Nat := (Poly.strip kp).deg.toNat
            for i in [:nA] do
              let di := (Poly.strip cps[i]!).deg.toNat
              if di > maxD then maxD := di
            let mut rowsA : Array (Array Expr) := Array.empty
            let mut rowsB : Array (Array Expr) := Array.empty
            for pwr in [:maxD + 1] do
              let mut row : Array Expr := Array.empty
              let mut any := false
              for i in [:nA] do
                let cij := Poly.coeff cps[i]! pwr
                if !(cij.isZero) then any := true
                row := row.push (ofRat cij)
              let kj := Poly.coeff kp pwr
              if !(kj.isZero) then any := true
              if any then
                rowsA := rowsA.push row
                rowsB := rowsB.push #[ofRat (RatConst.neg kj)]
            if rowsA.isEmpty then
              pure (some zero)
            else
              match Mat.solve rowsA rowsB with
              | .unique sol =>
                let mut yp := yp0
                for i in [:nA] do
                  yp := subst yp names[i]! (simplify (Mat.get! sol i 0))
                pure (some (simplify yp))
              | _ => pure none
        | _, _ => none

/-- Match `amp · q^n`. -/
partial def matchGeomForce? (e : Expr) (idx : String) : Option (Expr × Expr) :=
  go (simplify e)
where
  go : Expr → Option (Expr × Expr)
  | pow q (var v) =>
    if v == idx && !dependsOn q idx then some (one, simplify q) else none
  | pow (var v) _q =>
    if v == idx then none
    else none
  | mul (const k) rest =>
    match go rest with
    | some (amp, q) => some (simplify (mul (const k) amp), q)
    | none => none
  | mul rest (const k) => go (mul (const k) rest)
  | mul a b =>
    if !dependsOn a idx then
      match go b with
      | some (amp, q) => some (simplify (mul a amp), q)
      | none => none
    else if !dependsOn b idx then
      match go a with
      | some (amp, q) => some (simplify (mul b amp), q)
      | none => none
    else none
  | _ => none

/-- Undetermined coefficients for `amp · q^n`. -/
def recParticularGeom (as : Array RatConst) (amp q : Expr) (idx : String) : Option Expr :=
  let s := recRootMult as q
  let nv := var idx
  let qn := recPowN q idx
  let A := var "__ucG"
  let ns := if s == 0 then one else if s == 1 then nv else pow nv (ofNat s)
  let yp0 := mul (mul A ns) qn
  let K := recApplyOnGeom as s q idx
  -- L[A n^s q^n] = A K q^n; want A K = amp
  match affineForm (sub (mul A K) amp) ["__ucG"] with
  | some (cA, c0) =>
    if dependsOn cA[0]! idx || dependsOn c0 idx then none
    else if cA[0]! == zero || isZeroExpr cA[0]! idx then none
    else
      let Av := simplify (neg (div c0 cA[0]!))
      some (simplify (subst yp0 "__ucG" Av))
  | none => none

/-- Particular solution of `Σ a_k y(n+k) = g`. -/
def recParticular (as : Array RatConst) (g : Expr) (idx : String) : Except String Expr := do
  let g := simplify g
  if g == zero || isZeroExpr g idx then
    pure zero
  else
    match recParticularPoly as g idx with
    | some yp => pure yp
    | none =>
      match matchGeomForce? g idx with
      | some (amp, q) =>
        match recParticularGeom as amp q idx with
        | some yp => pure yp
        | none => throw "rsolve: could not find a particular solution for geometric forcing"
      | none =>
        throw "rsolve: forcing must be polynomial or geometric q^n"

/-- Dummy summation/product index, distinct from `idx`. -/
def recDummy (_idx : String) : String := "__k"

/-- Homogeneous factor `Π_{k=0}^{n−1} a(k)`. -/
def recHomFactor (a : Expr) (idx : String) : Except String Expr :=
  let k := recDummy idx
  let ak := subst a idx (var k)
  match prodFinite ak k zero (sub (var idx) one) with
  | some p => pure (simplify p)
  | none => throw s!"rsolve: no closed form for ∏ {a}"

/--
  First-order `A(n) y(n+1) + B(n) y(n) + D(n) = 0`,
  i.e. `y(n+1) = a(n) y(n) + b(n)` with `a=−B/A`, `b=−D/A`.
-/
def rsolveFirstOrderVar (B A D : Expr) (y idx : String) : Except String Expr := do
  if isZeroExpr A idx then
    throw "rsolve: coefficient of y(n+1) is zero"
  else
    let a := simplify (neg (div B A))
    let b := simplify (neg (div D A))
    let P ← recHomFactor a idx
    if b == zero || isZeroExpr b idx then
      pure (tidyODESol (eq (var y) (simplify (mul odeC P))))
    else
      let k := recDummy idx
      let bk := subst b idx (var k)
      let Pk1 := subst P idx (add (var k) one)
      if Pk1 == zero || isZeroExpr Pk1 k then
        throw "rsolve: vanishing product factor in variation of parameters"
      else
        let term := simplify (div bk Pk1)
        match sumFinite term k zero (sub (var idx) one) with
        | none => throw s!"rsolve: no closed form for ∑ {term}"
        | some S =>
          pure (tidyODESol (eq (var y) (simplify (mul P (add odeC S)))))

/-- Constant-coefficient scalar recurrence. -/
def rsolveConstCoeff (as : Array RatConst) (D : Expr) (y idx : String) :
    Except String Expr := do
  let d := as.size - 1
  if as.size == 0 || as[d]!.isZero then
    throw "rsolve: expected a non-trivial recurrence"
  else
    let p : Poly := ⟨as⟩
    let roots := charRootsWithMult p
    let got := roots.foldl (fun acc (_, m) => acc + m) 0
    if got < d then
      throw "rsolve: could not solve the characteristic equation"
    else
      let us := recBasis roots idx
      if us.length != d then
        throw s!"rsolve: expected {d} basis functions, got {us.length}"
      else
        let yh := recCombo us
        let g := simplify (neg D)
        let yp ← recParticular as g idx
        pure (tidyODESol (eq (var y) (simplify (add yh yp))))

def rsolveScalar (e : Expr) (y idx : String) : Except String Expr :=
  let e0 := equationToZero (simplify e)
  match linearFormInSeq e0 y idx with
  | none => throw "rsolve: expected a linear recurrence in y(n), y(n+1), …"
  | some (cs, D) =>
    if collectSeqVars D |>.any (fun t => t.1 == y) then
      throw "rsolve: nonlinear in y(n+k)"
    else
      match sliceNonzeroCoeffs cs with
      | none => throw "rsolve: expected a non-trivial recurrence"
      | some as =>
        if as.size < 2 then
          throw "rsolve: expected order ≥ 1"
        else
          match ratCoeffArray? as with
          | some ras => rsolveConstCoeff ras D y idx
          | none =>
            if as.size == 2 then
              rsolveFirstOrderVar as[0]! as[1]! D y idx
            else
              throw "rsolve: variable coefficients are only supported for first-order recurrences"

/-- Apply `ics[k] = y(k)` for `k = 0, 1, …`. -/
def applyRecICs (sol : Expr) (y idx : String) (ics : List Expr) : Except String Expr :=
  match asEquation? sol with
  | none => throw "rsolve IC: expected explicit solution y = …"
  | some (lhs, rhs) =>
    if lhs != var y then throw "rsolve IC: expected y = …"
    else
      let cs := collectOdeCs rhs
      if cs.isEmpty then
        pure (tidyODESol sol)
      else if ics.length != cs.length then
        throw s!"rsolve IC: expected {cs.length} initial values y(0), y(1), …, got {ics.length}"
      else
        let eqs : List Expr :=
          Id.run do
            let mut out : List Expr := []
            for k in [:ics.length] do
              let atk := simplify (subst rhs idx (ofNat k))
              out := out ++ [eq atk ics[k]!]
            pure out
        match solveLinearSystem eqs (some cs) with
        | .error msg => throw s!"rsolve IC: {msg}"
        | .ok named =>
          let rhs' : Option Expr :=
            Id.run do
              let mut out := rhs
              for c in cs do
                match namedGet? named c with
                | none => return none
                | some val => out := subst out c val
              some out
          match rhs' with
          | none => throw "rsolve IC: could not extract constants"
          | some rhs' =>
            pure (tidyODESol (eq (var y) (simplify rhs')))

def rsolveICs (e : Expr) (y idx : String) (ics : List Expr) : Except String Expr := do
  let sol ← rsolveScalar e y idx
  applyRecICs sol y idx ics

/-- `Y(n) = A^n C` as named `y1, y2, …`. -/
def rsolveLinSys (A : Array (Array Expr)) (idx : String := "n") : Except String Expr := do
  let n := Mat.nrows A
  if n == 0 || n != Mat.ncols A then
    throw "rsolve: system matrix must be square and non-empty"
  else
    let An ← Mat.powAt A (var idx)
    let C :=
      Id.run do
        let mut rows : Array (Array Expr) := Array.empty
        for i in [:n] do
          rows := rows.push #[odeCi i]
        pure rows
    match Mat.mul An C with
    | none => throw "rsolve: A^n · C shape error"
    | some Y => pure (packYEqs Y)

/-- `Y(n) = A^n Y0`. -/
def rsolveLinSysIC (A Y0 : Array (Array Expr)) (idx : String := "n") :
    Except String Expr := do
  let n := Mat.nrows A
  if n == 0 || n != Mat.ncols A then
    throw "rsolve: system matrix must be square"
  else
    match asColVec? Y0 n with
    | none => throw s!"rsolve: initial vector must be {n}×1 (or 1×{n})"
    | some y0 =>
      let An ← Mat.powAt A (var idx)
      match Mat.mul An y0 with
      | none => throw "rsolve: A^n · Y0 shape error"
      | some Y => pure (packYEqs Y)

/-- Constant particular `Yp = (I−A)⁻¹ g` when `1` is not an eigenvalue. -/
def particularConstRecSys (A g : Array (Array Expr)) (idx : String) :
    Option (Array (Array Expr)) :=
  let n := Mat.nrows A
  match Mat.sub (Mat.eye n) A with
  | none => none
  | some M =>
    match Mat.det M with
    | none => none
    | some d =>
      let d := simplify d
      if d == zero || isZeroExpr d idx then none
      else
        match Mat.inv M with
        | none => none
        | some Minv =>
          match Mat.mul (matSimplify Minv) g with
          | none => none
          | some Yp => some (matSimplify Yp)

/-- Entrywise `∑_{k=lo}^{hi}`. -/
def sumMat (m : Array (Array Expr)) (k : String) (lo hi : Expr) :
    Except String (Array (Array Expr)) := do
  let mut out : Array (Array Expr) := Array.empty
  for row in m do
    let mut r : Array Expr := Array.empty
    for e in row do
      match sumFinite e k lo hi with
      | some s => r := r.push (simplify s)
      | none => throw s!"rsolve: no closed form for ∑ {e}"
    out := out.push r
  pure out

/-- Discrete VoP: `Yp = A^n ∑_{k=0}^{n−1} A^{−(k+1)} g(k)` (`A` invertible). -/
def variationRecSys (A g : Array (Array Expr)) (idx : String) :
    Except String (Array (Array Expr)) := do
  match Mat.inv A with
  | none => throw "rsolve: variation of parameters needs invertible A"
  | some Ainv =>
    let k := recDummy idx
    let gk := Mat.map g (fun e => simplify (subst e idx (var k)))
    let Bpow ← Mat.powAt (matSimplify Ainv) (add (var k) one)
    match Mat.mul Bpow gk with
    | none => throw "rsolve: A⁻⁽ᵏ⁺¹⁾·g shape error"
    | some w =>
      let U ← sumMat (matSimplify w) k zero (sub (var idx) one)
      let An ← Mat.powAt A (var idx)
      match Mat.mul An U with
      | none => throw "rsolve: A^n · U shape error"
      | some Yp => pure (matSimplify Yp)

/-- Particular `Yp` for `Y(n+1) = A Y(n) + g`. -/
def particularRecSys (A g : Array (Array Expr)) (idx : String) :
    Except String (Array (Array Expr)) :=
  if !matDependsOn g idx then
    match particularConstRecSys A g idx with
    | some yp => pure yp
    | none => variationRecSys A g idx
  else
    variationRecSys A g idx

/-- Solve `Y(n+1) = A Y(n) + g(n)`. -/
def rsolveLinSysNonhom (A g : Array (Array Expr)) (idx : String := "n") :
    Except String Expr :=
  let n := Mat.nrows A
  if n == 0 || n != Mat.ncols A then
    throw "rsolve: system matrix must be square and non-empty"
  else
    match asColVec? g n with
    | none => throw s!"rsolve: forcing g must be {n}×1 (or 1×{n})"
    | some g => do
      let An ← Mat.powAt A (var idx)
      let Yp ← particularRecSys A g idx
      match Mat.mul An (cCol n) with
      | none => throw "rsolve: A^n · C shape error"
      | some Yh =>
        match Mat.add Yh Yp with
        | none => throw "rsolve: Yh+Yp shape error"
        | some Y => pure (packYEqs Y)

/-- Solve `Y(n+1) = A Y(n) + g` with `Y(0) = Y0`. -/
def rsolveLinSysNonhomIC (A g Y0 : Array (Array Expr)) (idx : String := "n") :
    Except String Expr :=
  let n := Mat.nrows A
  if n == 0 || n != Mat.ncols A then
    throw "rsolve: system matrix must be square"
  else
    match asColVec? g n, asColVec? Y0 n with
    | none, _ => throw s!"rsolve: forcing g must be {n}×1 (or 1×{n})"
    | _, none => throw s!"rsolve: initial vector must be {n}×1 (or 1×{n})"
    | some g, some y0 => do
      let An ← Mat.powAt A (var idx)
      let Yp ← particularRecSys A g idx
      let Yp0 := Mat.map Yp (fun e => simplify (subst e idx zero))
      match Mat.sub y0 Yp0 with
      | none => throw "rsolve: Y0 − Yp(0) shape error"
      | some C =>
        match Mat.mul An C with
        | none => throw "rsolve: A^n · C shape error"
        | some Yh =>
          match Mat.add Yh Yp with
          | none => throw "rsolve: Yh+Yp shape error"
          | some Y => pure (packYEqs Y)

def asPlainVar? : Expr → Option String
  | var v =>
    if (parseSeqVar? v).isSome then none else some v
  | _ => none

def asSeqHead? : Expr → Option (String × String)
  | var v =>
    match parseSeqVar? v with
    | some (y, n, _) => some (y, n)
    | none => none
  | _ => none

/-- Peel optional `y(n)` / `y, n` from `rsolve` arguments. -/
def peelRsolveArgs (args : List Expr) (yDef idxDef : String) :
    String × String × List Expr :=
  match args with
  | a :: rest =>
    match asSeqHead? a with
    | some (y, idx) => (y, idx, rest)
    | none =>
      match asPlainVar? a with
      | some y =>
        match rest with
        | b :: rest2 =>
          match asPlainVar? b with
          | some idx => (y, idx, rest2)
          | none => (y, idxDef, rest)
        | [] => (y, idxDef, [])
      | none => (yDef, idxDef, args)
  | [] => (yDef, idxDef, [])

/-- Homogeneous operator `∑ bs[i] y(n+i) = 0`. -/
def rsolveHomOp (bs : Array Expr) (y idx : String) : Except String Expr :=
  match sliceNonzeroCoeffs bs with
  | none => throw "rsolve: trivial recurrence"
  | some as =>
    if as.size < 2 then
      throw "rsolve: expected order ≥ 1"
    else
      match ratCoeffArray? as with
      | some ras => rsolveConstCoeff ras zero y idx
      | none =>
        if as.size == 2 then
          rsolveFirstOrderVar as[0]! as[1]! zero y idx
        else
          throw "rsolve: variable coefficients are only supported for first-order recurrences"

/-- Parameter name for a summand `F` besides the index `k`. -/
def inferSumParam (F lo hi : Expr) (k : String) : String :=
  let vs :=
    (freeVars F ++ freeVars lo ++ freeVars hi).filter (fun v => v != k)
  if vs.contains "n" then "n"
  else match vs with | v :: _ => v | [] => "n"

/-- Evaluate `∑_{k=lo}^{hi} F` at a numeric parameter value. -/
def evalSumAt (F : Expr) (k n : String) (lo hi : Expr) (nVal : Int) : Option Expr :=
  let Fn := subst F n (ofInt nVal)
  let lo' := subst lo n (ofInt nVal)
  let hi' := subst hi n (ofInt nVal)
  match asIntConstExpr lo', asIntConstExpr hi' with
  | some a, some b => sumBrute Fn k a b
  | _, _ => none

/--
  Closed form for `∑_{k=lo}^{hi} F` via Zeilberger + `rsolve`, when
  `F` is hypergeometric in `k` and a discrete parameter (usually `n`).
-/
def zeilbergerSum (F : Expr) (k : String) (lo hi : Expr) : Option Expr :=
  let n := inferSumParam F lo hi k
  if n == k || !dependsOn F n then none
  else
    match zeilbergerOp? F n k with
    | none => none
    | some bs =>
      match rsolveHomOp bs "f" n with
      | .error _ => none
      | .ok sol =>
        match asEquation? sol with
        | none => none
        | some (lhs, rhs) =>
          if lhs != var "f" then none
          else
            let cs := collectOdeCs rhs
            if cs.isEmpty then some (simplify rhs)
            else
              let ics : Option (List Expr) :=
                Id.run do
                  let mut out : List Expr := []
                  for t in [:cs.length] do
                    match evalSumAt F k n lo hi (Int.ofNat t) with
                    | none => return none
                    | some v => out := out ++ [v]
                  some out
              match ics with
              | none => none
              | some ics =>
                match applyRecICs sol "f" n ics with
                | .error _ => none
                | .ok sol' =>
                  match asEquation? sol' with
                  | some (_, r) => some (simplify r)
                  | none => none

/-- `sumFinite`, then Zeilberger if that fails. -/
def sumClosedForm (body : Expr) (k : String) (lo hi : Expr) : Except String Expr :=
  match sumFinite body k lo hi with
  | some s => pure s
  | none =>
    match zeilbergerSum body k lo hi with
    | some s => pure s
    | none => throw s!"no closed form for sum over {k} of {body}"

/-- Dispatch `rsolve(eq, …)` from parsed arguments. -/
def rsolveFromArgs (e : Expr) (args : List Expr) : Except String Expr :=
  match asMat? e with
  | some A =>
    match args with
    | [] => rsolveLinSys A "n"
    | [a] =>
      match asMat? a with
      | some V =>
        if matDependsOn V "n" then rsolveLinSysNonhom A V "n"
        else rsolveLinSysIC A V "n"
      | none =>
        match asPlainVar? a with
        | some idx => rsolveLinSys A idx
        | none => throw "rsolve: expected rsolve(A) or rsolve(A, Y0)"
    | [a, b] =>
      match asMat? a, asMat? b with
      | some g, some Y0 => rsolveLinSysNonhomIC A g Y0 "n"
      | some g, none =>
        match asPlainVar? b with
        | some idx => rsolveLinSysNonhom A g idx
        | none => throw "rsolve: expected rsolve(A, g, Y0) or rsolve(A, g, n)"
      | none, _ => throw "rsolve: expected rsolve(A, g, Y0) or rsolve(A, g, n)"
    | _ => throw "rsolve: too many arguments for a linear system"
  | none =>
    let (yDef, nDef) := inferSeqNames? e |>.getD ("y", "n")
    let (y, idx, rest) := peelRsolveArgs args yDef nDef
    if rest.isEmpty then
      rsolveScalar e y idx
    else
      rsolveICs e y idx rest

end Taschenrechner
