/-
  Scalar polynomial solving and factoring over ℚ.

  * `factor` — factor polynomials / rationals in one variable (and small integers)
  * `roots` / `solve` — rational roots + quadratic formula for remaining deg-2 pieces
  * `coeff` / `collect` — coefficient extraction and poly collection
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Poly
import Taschenrechner.RatInt
import Taschenrechner.Normal
import Taschenrechner.Matrix
import Taschenrechner.LinAlg

namespace Taschenrechner

open Expr

/-! ### Helpers -/

/-- Integer square root test for a non-negative rational. -/
def ratSqrt? (r : RatConst) : Option RatConst :=
  let r := RatConst.normalize r
  if r.num < 0 then none
  else
    let sn := Nat.sqrt r.num.natAbs
    let sd := Nat.sqrt r.den
    if sn * sn == r.num.natAbs && sd * sd == r.den && sd ≠ 0 then
      some (RatConst.normalize ⟨(sn : Int), sd⟩)
    else none

/-- Trial factorization of a positive natural. -/
partial def factorNat (n : Nat) : List (Nat × Nat) :=
  if n ≤ 1 then []
  else
    let rec go (n p : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
      if n == 1 then acc.reverse
      else if p * p > n then
        if n > 1 then ((n, 1) :: acc).reverse else acc.reverse
      else if n % p == 0 then
        let rec count (n e : Nat) : Nat × Nat :=
          if n % p == 0 then count (n / p) (e + 1) else (n, e)
        let (n', e) := count n 0
        go n' (p + 1) ((p, e) :: acc)
      else go n (p + 1) acc
    go n 2 []

/--
  Factor a non-zero integer as a matrix of `[prime, exponent]` rows
  (survives auto-`simplify`, which would fold `2^2·3` back to `12`).
  Negative `n` gets a leading row `[-1, 1]`.
-/
def factorInt (n : Int) : Expr :=
  if n == 0 then Expr.zero
  else if n == 1 then Expr.one
  else if n == -1 then Expr.negOne
  else
    let facs := factorNat n.natAbs
    let rows : List (Array Expr) :=
      facs.map fun (p, e) => #[Expr.ofNat p, Expr.ofNat e]
    let rows :=
      if n < 0 then #[Expr.ofInt (-1), Expr.ofNat 1] :: rows else rows
    if rows.isEmpty then Expr.one
    else Expr.mat rows.toArray

/-- Convert expression to a polynomial in `v` (clears a constant denominator). -/
def asPolyIn? (e : Expr) (v : String) : Option Poly :=
  match RatFn.ofExpr? (simplify e) v with
  | none => none
  | some r =>
    let r := RatFn.simplify r
    if r.num.isZero then some Poly.zero
    else if r.den.isOne then some (Poly.strip r.num)
    else if r.den.deg == 0 then
      let d := Poly.coeff r.den 0
      match RatConst.inv d with
      | some inv => some (Poly.strip (Poly.scale inv r.num))
      | none => none
    else
      -- rational: zeros of num (excluding poles); use numerator
      some (Poly.strip r.num)

/-- Build monic linear factor `x − r`. -/
def linearFactor (v : String) (r : RatConst) : Expr :=
  if r.isZero then var v
  else if r.isNegOne then add (var v) one
  else if r.num < 0 then
    -- x - (-|r|) = x + |r|
    add (var v) (ofRat (RatConst.neg r))
  else
    sub (var v) (ofRat r)

/-- Group equal monic factors with multiplicity. -/
def groupFactors (fs : List Poly) : List (Poly × Nat) :=
  let rec insert (p : Poly) : List (Poly × Nat) → List (Poly × Nat)
    | [] => [(p, 1)]
    | (q, m) :: rest =>
      if p == q then (q, m + 1) :: rest
      else (q, m) :: insert p rest
  fs.foldl (fun acc p => insert (Poly.monic p) acc) []

/-- Product of (poly factor expressions) with multiplicities. -/
def factorsToExpr (c : RatConst) (facs : List (Poly × Nat)) (v : String) : Expr :=
  let body :=
    facs.foldl (fun acc (p, m) =>
      let pe := Poly.toExpr p v
      let pe := if m == 1 then pe else pow pe (Expr.ofNat m)
      if acc == Expr.one then pe else mul acc pe) Expr.one
  if c.isOne then body
  else if c.isZero then Expr.zero
  else if body == Expr.one then Expr.ofRat c
  else mul (Expr.ofRat c) body

/-! ### Factor -/

/-- Factor a univariate polynomial/rational expression over ℚ in variable `v`. -/
def factorIn (e : Expr) (v : String) : Option Expr :=
  let e := simplify e
  -- pure integer constant
  match e with
  | const c =>
    match CplxConst.toRat? c with
    | some q =>
      if q.den == 1 then some (factorInt q.num)
      else
        -- p/q: return factor matrices is awkward; leave as factored ints product
        -- via num/den integer matrices is unclear — emit (factor num)/(factor den)
        -- only when both are ±1 or use poly path; for fractions use num/den ints.
        some (div (factorInt q.num) (factorInt (Int.ofNat q.den)))
    | none => some e  -- complex constant: leave
  | _ =>
    match RatFn.ofExpr? e v with
    | none => none
    | some r =>
      let r := RatFn.simplify r
      if r.num.isZero then some Expr.zero
      else
        let (cn, nFacs) := Poly.factorOverQ r.num
        let (cd, dFacs) := Poly.factorOverQ r.den
        let nG := groupFactors nFacs
        let dG := groupFactors dFacs
        -- Do not `simplify` the product: that would reassemble integers
        -- (2²·3 → 12) and can expand linear factors.
        let numE := factorsToExpr cn nG v
        if r.den.isOne || (dFacs.isEmpty && cd.isOne) then
          some numE
        else
          let denE := factorsToExpr cd dG v
          some (div numE denE)

def factor (e : Expr) (v : String := "x") : Expr :=
  match factorIn e v with
  | some f => f
  | none => simplify e

/-! ### Roots & solve -/

/-- Extract rational roots (with multiplicity) from factorOverQ linear factors. -/
def rationalRoots (p : Poly) : List RatConst :=
  let (_c, facs) := Poly.factorOverQ p
  facs.filterMap fun f =>
    let f := Poly.monic (Poly.strip f)
    -- monic linear: x − r  ≡  ⟨−r, 1⟩
    if f.deg == 1 && (Poly.coeff f 1).isOne then
      some (RatConst.neg (Poly.coeff f 0))
    else none

/-- Quadratic formula for `a x² + b x + c = 0` with `a ≠ 0`. -/
def quadraticRoots (a b c : RatConst) : List Expr :=
  match RatConst.inv a with
  | none => []
  | some _ =>
    let disc := b * b - RatConst.ofInt 4 * a * c
    let twoA := RatConst.ofInt 2 * a
    match RatConst.inv twoA with
    | none => []
    | some inv2a =>
      let negB := RatConst.neg b
      if disc.isZero then
        [Expr.ofRat (negB * inv2a)]
      else
        match ratSqrt? disc with
        | some s =>
          [Expr.ofRat ((negB + s) * inv2a), Expr.ofRat ((negB - s) * inv2a)]
        | none =>
          if disc.num < 0 then
            -- complex: (-b ± i √|disc|) / (2a)
            match ratSqrt? (RatConst.neg disc) with
            | some s =>
              let re := Expr.ofRat (negB * inv2a)
              let im := Expr.ofRat (s * inv2a)
              let iim := mul I im
              [simplify (add re iim), simplify (sub re iim)]
            | none =>
              -- fallback symbolic sqrt of negative
              let s := sqrt (Expr.ofRat (RatConst.neg disc))
              let re := Expr.ofRat (negB * inv2a)
              let im := simplify (mul (Expr.ofRat inv2a) s)
              let iim := mul I im
              [simplify (add re iim), simplify (sub re iim)]
          else
            -- real irrational
            let s := sqrt (Expr.ofRat disc)
            let half := Expr.ofRat inv2a
            let mid := Expr.ofRat (negB * inv2a)
            [simplify (add mid (mul half s)), simplify (sub mid (mul half s))]

/--
  Roots of a univariate poly over ℚ, with quadratic formula for irreducible
  quadratics. Higher-degree irreducibles yield no closed roots here.
-/
def rootsPoly (p : Poly) : List Expr :=
  let p := Poly.strip p
  if p.isZero then []  -- identity; handled by caller
  else if p.deg < 0 then []
  else if p.deg == 0 then []  -- non-zero constant: no roots
  else
    let (c, facs) := Poly.factorOverQ p
    let _ := c
    Id.run do
      let mut out : List Expr := []
      for f in facs do
        let f := Poly.monic (Poly.strip f)
        if f.deg == 1 && (Poly.coeff f 1).isOne then
          out := Expr.ofRat (RatConst.neg (Poly.coeff f 0)) :: out
        else if f.deg == 2 then
          let a := Poly.coeff f 2
          let b := Poly.coeff f 1
          let c0 := Poly.coeff f 0
          out := quadraticRoots a b c0 ++ out
        else
          pure ()
      pure out.reverse

inductive ScalarSolveResult where
  /-- Finite list of solutions. -/
  | solutions : List Expr → ScalarSolveResult
  /-- Every value is a solution (0 = 0). -/
  | all : ScalarSolveResult
  /-- No solutions (non-zero constant = 0). -/
  | empty : ScalarSolveResult
  /-- Could not interpret as a univariate rational equation. -/
  | unsupported : String → ScalarSolveResult
  deriving Repr

namespace ScalarSolveResult

def toExpr : ScalarSolveResult → Expr
  | .solutions rs =>
    -- 1×n row matrix of roots (empty → 1×0)
    Expr.mat #[rs.toArray]
  | .all => var "all"  -- marker; parser may special-case
  | .empty => Expr.mat #[#[] ]
  | .unsupported _ => Expr.zero

def toString : ScalarSolveResult → String
  | .solutions rs =>
    if rs.isEmpty then "∅"
    else String.intercalate ", " (rs.map fun r => s!"{r}")
  | .all => "all (identity)"
  | .empty => "∅ (no solution)"
  | .unsupported msg => s!"unsupported: {msg}"

end ScalarSolveResult

/-- Solve `e = 0` as a univariate rational equation in `v`. -/
def solveScalar (e : Expr) (v : String) : ScalarSolveResult :=
  let e := simplify e
  match asPolyIn? e v with
  | none => .unsupported s!"not a rational expression in {v}"
  | some p =>
    let p := Poly.strip p
    if p.isZero then .all
    else if p.deg == 0 then .empty  -- non-zero constant
    else
      let rs := rootsPoly p
      -- If deg > 2 irreducible pieces remain unsolved, still return what we found
      .solutions (rs.map simplify)

/-- Solve `lhs = rhs` in `v`. -/
def solveEq (lhs rhs : Expr) (v : String) : ScalarSolveResult :=
  solveScalar (sub lhs rhs) v

/-- Roots of `e = 0` as a list (empty if none / identity / unsupported). -/
def roots (e : Expr) (v : String := "x") : List Expr :=
  match solveScalar e v with
  | .solutions rs => rs
  | _ => []

/--
  Convert a scalar solve result to an expression for the REPL:
  * finite roots → 1×n matrix
  * empty → empty row matrix
  * all → the symbol `all` (variable)
  * unsupported → error via Option
-/
def solveScalarExpr? (e : Expr) (v : String) : Except String Expr :=
  match solveScalar e v with
  | .solutions rs => pure (Expr.mat #[rs.toArray])
  | .all => pure (var "all")
  | .empty => pure (Expr.mat #[#[] ])
  | .unsupported msg => throw msg

def solveEqExpr? (lhs rhs : Expr) (v : String) : Except String Expr :=
  solveScalarExpr? (sub lhs rhs) v

/-! ### coeff / collect -/

/-- Coefficient of `v^n` in a polynomial/rational (num after clear const den). -/
def coeffOf (e : Expr) (v : String) (n : Nat) : Option Expr :=
  match asPolyIn? e v with
  | some p => some (Expr.ofRat (Poly.coeff p n))
  | none => none

/-- Collect terms as a canonical polynomial in `v` (when possible). -/
def collectIn (e : Expr) (v : String) : Option Expr :=
  match asPolyIn? e v with
  | some p => some (simplify (Poly.toExpr p v))
  | none =>
    match RatFn.ofExpr? (simplify e) v with
    | some r => some (RatFn.toExpr (RatFn.simplify r) v)
    | none => none

def collect (e : Expr) (v : String := "x") : Expr :=
  match collectIn e v with
  | some f => f
  | none => simplify e

/-! ### Linear systems -/

/-- Unit coefficient vector for variable index `i`. -/
def unitCoeffs (n i : Nat) : Array Expr :=
  Id.run do
    let mut a : Array Expr := Array.replicate n zero
    if i < n then a := a.set! i one
    pure a

/-- Zero coefficient vector. -/
def zeroCoeffs (n : Nat) : Array Expr :=
  Array.replicate n zero

/--
  Parse `e` as an affine form ∑ cᵢ·vᵢ + k in the given variables.
  Returns `(coeffs, constant)` so that e = ∑ cᵢ vᵢ + k.
-/
def indexOf (name : String) (vars : List String) : Option Nat :=
  let rec go (i : Nat) : List String → Option Nat
    | [] => none
    | v :: rest => if v == name then some i else go (i + 1) rest
  go 0 vars

partial def affineForm (e : Expr) (vars : List String) : Option (Array Expr × Expr) :=
  go (simplify e) vars.length
where
  go : Expr → Nat → Option (Array Expr × Expr)
  | add a b, n =>
    match go a n, go b n with
    | some (ca, ka), some (cb, kb) =>
      some (
        Id.run do
          let mut out := ca
          for i in [:n] do
            out := out.set! i (simplify (add ca[i]! cb[i]!))
          pure out,
        simplify (add ka kb))
    | _, _ => none
  | mul (const c) rest, n =>
    match go rest n with
    | some (cs, k) =>
      some (cs.map fun ci => simplify (mul (const c) ci), simplify (mul (const c) k))
    | none => none
  | mul rest (const c), n => go (mul (const c) rest) n
  | var name, n =>
    match indexOf name vars with
    | some i => some (unitCoeffs n i, zero)
    | none =>
      -- treat other free symbols as constant terms
      some (zeroCoeffs n, var name)
  | const c, n => some (zeroCoeffs n, const c)
  | e, n =>
    if vars.any (fun v => dependsOn e v) then
      -- product of one var and a coefficient free of all vars
      match e with
      | mul a b =>
        let aDep := vars.any (fun v => dependsOn a v)
        let bDep := vars.any (fun v => dependsOn b v)
        if aDep && !bDep then
          match go a n with
          | some (cs, k) =>
            if k == zero then
              some (cs.map fun ci => simplify (mul ci b), zero)
            else none
          | none => none
        else if bDep && !aDep then
          match go b n with
          | some (cs, k) =>
            if k == zero then
              some (cs.map fun ci => simplify (mul ci a), zero)
            else none
          | none => none
        else none
      | _ => none
    else
      some (zeroCoeffs n, e)

/-- Collect free variables appearing in any of the expressions, sorted. -/
def collectVars (es : List Expr) : List String :=
  es.foldl (fun acc e => (acc ++ freeVars e).eraseDups) []
    |>.mergeSort (· < ·)

/-- Pack a column of values into named equations `vᵢ = valᵢ`. -/
def namedSolution (vars : List String) (x : Array (Array Expr)) : Expr :=
  let n := vars.length
  let rows : Array (Array Expr) :=
    Id.run do
      let mut out : Array (Array Expr) := Array.empty
      for i in [:n] do
        let name := vars[i]!
        let val :=
          if i < Mat.nrows x && Mat.ncols x ≥ 1 then
            simplify (Mat.get! x i 0)
          else zero
        out := out.push #[eq (var name) val]
      pure out
  Expr.mat rows

/--
  Solve a system of linear equations (each entry an equation or residual = 0).
  Returns an n×1 column of **named equations** `vᵢ = …` in the given variable
  order (or inferred free variables, sorted alphabetically).
-/
def solveLinearSystem (eqs : List Expr) (vars? : Option (List String) := none) :
    Except String Expr :=
  if eqs.isEmpty then throw "solve: empty system"
  else
    let residuals := eqs.map fun e =>
      match asEquation? e with
      | some (a, b) => simplify (sub a b)
      | none => simplify e
    let vars :=
      match vars? with
      | some vs => vs
      | none => collectVars residuals
    if vars.isEmpty then throw "solve: no free variables in system"
    else
      let n := vars.length
      let m := residuals.length
      let built : Option (Array (Array Expr) × Array (Array Expr)) :=
        Id.run do
          let mut rowsA : Array (Array Expr) := Array.empty
          let mut rowsB : Array (Array Expr) := Array.empty
          for r in residuals do
            match affineForm r vars with
            | none => return none
            | some (cs, k) =>
              -- ∑ cᵢ vᵢ + k = 0  →  ∑ cᵢ vᵢ = −k
              rowsA := rowsA.push cs
              rowsB := rowsB.push #[simplify (neg k)]
          pure (some (rowsA, rowsB))
      match built with
      | none => throw s!"solve: nonlinear or unsupported equation in system"
      | some (A, b) =>
        if Mat.nrows A != m || Mat.ncols A != n then
          throw "solve: internal shape error"
        else
          match Mat.solve A b with
          | .unique x => pure (namedSolution vars x)
          | .general x _ => pure (namedSolution vars x)
          | .inconsistent msg => throw s!"solve: {msg}"
          | .error msg => throw s!"solve: {msg}"

/-! ### Inequalities (univariate poly) + interval merge -/

/-- Compare two real rational expressions for ordering (only rational constants). -/
def ratExprCompare (a b : Expr) : Option Ordering :=
  match simplify a, simplify b with
  | const ca, const cb =>
    match CplxConst.toRat? ca, CplxConst.toRat? cb with
    | some ra, some rb => some (RatConst.compare ra rb)
    | _, _ => none
  | _, _ => none

/-- Sort a list of rational constant expressions ascending. -/
def sortRatExprs (xs : List Expr) : List Expr :=
  xs.toArray.qsort (fun a b =>
    match ratExprCompare a b with
    | some .lt => true
    | _ => false) |>.toList

/-- Sign of a poly at a rational test point (after simplify). -/
def polySignAt (p : Poly) (t : RatConst) : Option Bool :=
  let v := Poly.eval p t
  if v.isZero then none
  else some (v.num > 0)

/-- Midpoint of two rationals (or offset if infinite). -/
def midPoint (a b : Option RatConst) : RatConst :=
  match a, b with
  | none, none => RatConst.zero
  | none, some r => r - 1  -- left of first root
  | some r, none => r + 1  -- right of last root
  | some lo, some hi =>
    match RatConst.div (lo + hi) (RatConst.ofInt 2) with
    | some m => m
    | none => lo

/-- Real interval with optional infinite ends and open/closed flags. -/
structure RealInterval where
  lo       : Option RatConst  -- none = −∞
  hi       : Option RatConst  -- none = +∞
  loClosed : Bool
  hiClosed : Bool
  deriving Repr, Inhabited

namespace RealInterval

def isEmpty (I : RealInterval) : Bool :=
  match I.lo, I.hi with
  | some a, some b =>
    match RatConst.compare a b with
    | .gt => true
    | .eq => !(I.loClosed && I.hiClosed)
    | .lt => false
  | _, _ => false

def isPoint (I : RealInterval) : Bool :=
  match I.lo, I.hi with
  | some a, some b => a == b && I.loClosed && I.hiClosed
  | _, _ => false

/-- Compare lo endpoints for sorting (−∞ first). -/
def loLess (a b : RealInterval) : Bool :=
  match a.lo, b.lo with
  | none, none =>
    -- same lo −∞: open before closed is irrelevant; use hi
    true
  | none, some _ => true
  | some _, none => false
  | some ra, some rb =>
    match RatConst.compare ra rb with
    | .lt => true
    | .gt => false
    | .eq =>
      -- closed lo sorts before open lo (smaller set-start)
      a.loClosed && !b.loClosed

/-- Does `I` contain the rational point `r`? -/
def containsRat (I : RealInterval) (r : RatConst) : Bool :=
  let leftOk :=
    match I.lo with
    | none => true
    | some a =>
      match RatConst.compare a r with
      | .lt => true
      | .eq => I.loClosed
      | .gt => false
  let rightOk :=
    match I.hi with
    | none => true
    | some b =>
      match RatConst.compare r b with
      | .lt => true
      | .eq => I.hiClosed
      | .gt => false
  leftOk && rightOk

/--
  Can `A` and `B` (sorted, A.lo ≤ B.lo) be merged into one interval?
  Adjacent intervals merge if they overlap or touch at an included endpoint.
-/
def canMerge (A B : RealInterval) : Bool :=
  match A.hi, B.lo with
  | none, _ => true  -- A goes to +∞
  | some _, none => true  -- B from −∞ (shouldn't if sorted)
  | some ah, some bl =>
    match RatConst.compare ah bl with
    | .gt => true  -- overlap
    | .lt => false  -- gap
    | .eq => A.hiClosed || B.loClosed  -- touch

def mergeTwo (A B : RealInterval) : RealInterval :=
  -- lo: earlier of the two
  let (lo, loC) :=
    match A.lo, B.lo with
    | none, _ => (none, A.loClosed)
    | _, none => (none, B.loClosed)
    | some ra, some rb =>
      match RatConst.compare ra rb with
      | .lt => (some ra, A.loClosed)
      | .gt => (some rb, B.loClosed)
      | .eq => (some ra, A.loClosed || B.loClosed)
  let (hi, hiC) :=
    match A.hi, B.hi with
    | none, _ => (none, A.hiClosed)
    | _, none => (none, B.hiClosed)
    | some ra, some rb =>
      match RatConst.compare ra rb with
      | .gt => (some ra, A.hiClosed)
      | .lt => (some rb, B.hiClosed)
      | .eq => (some ra, A.hiClosed || B.hiClosed)
  { lo := lo, hi := hi, loClosed := loC, hiClosed := hiC }

/-- Sort and merge overlapping/adjacent intervals. -/
def mergeAll (xs : List RealInterval) : List RealInterval :=
  let xs := xs.filter (fun I => !I.isEmpty)
  if xs.isEmpty then []
  else
    let sorted := xs.toArray.qsort loLess |>.toList
    Id.run do
      let mut acc : List RealInterval := []
      let mut cur := sorted.head!
      for I in sorted.tail do
        if canMerge cur I then
          cur := mergeTwo cur I
        else
          acc := acc ++ [cur]
          cur := I
      pure (acc ++ [cur])

def loExpr (I : RealInterval) : Expr :=
  match I.lo with
  | none => neg (var "∞")
  | some r => ofRat r

def hiExpr (I : RealInterval) : Expr :=
  match I.hi with
  | none => var "∞"
  | some r => ofRat r

/-- Encode as row `[lo, hi, loClosed, hiClosed]` with closed ∈ {0,1}. -/
def toRow (I : RealInterval) : Array Expr :=
  #[loExpr I, hiExpr I,
    ofInt (if I.loClosed then 1 else 0),
    ofInt (if I.hiClosed then 1 else 0)]

/-- Encode a list of intervals as an n×4 matrix (empty → 1×0). -/
def toExpr (xs : List RealInterval) : Expr :=
  match mergeAll xs with
  | [] => Expr.mat #[#[] ]
  | ys =>
    -- Whole real line?
    match ys with
    | [I] =>
      if I.lo.isNone && I.hi.isNone then var "all"
      else simplify (Expr.mat (ys.map toRow).toArray)
    | _ => simplify (Expr.mat (ys.map toRow).toArray)

end RealInterval

/-- Bound expression as optional rational (±∞ → none). -/
def asBoundRat? (e : Expr) : Option (Option RatConst) :=
  match simplify e with
  | const c =>
    match CplxConst.toRat? c with
    | some r => some (some r)
    | none => none
  | var v => if isInfName v then some none else none
  | mul (const _) (var v) =>
    if isInfName v then some none else none  -- ±∞
  | _ => none

/-- Parse an interval row (2-col legacy or 4-col with closed flags). -/
def parseIntervalRow? (row : Array Expr) : Option RealInterval :=
  if row.size == 2 || row.size == 4 then
    match asBoundRat? row[0]!, asBoundRat? row[1]! with
    | some lo, some hi =>
      let loC :=
        if row.size == 4 then
          match simplify row[2]! with
          | const c => !(c.isZero)
          | _ => true
        else true
      let hiC :=
        if row.size == 4 then
          match simplify row[3]! with
          | const c => !(c.isZero)
          | _ => true
        else true
      some { lo := lo, hi := hi, loClosed := loC, hiClosed := hiC }
    | _, _ => none
  else none

/-- Format one interval for display: `(a, b)`, `[a, b]`, `{a}`, … -/
def formatInterval (I : RealInterval) : String :=
  if I.isEmpty then "∅"
  else if I.isPoint then
    match I.lo with
    | some r => s!"\{{Expr.toString (ofRat r)}}"
    | none => "∅"
  else
    let ls := if I.loClosed then "[" else "("
    let rs := if I.hiClosed then "]" else ")"
    let loS :=
      match I.lo with
      | none => "-∞"
      | some r => Expr.toString (ofRat r)
    let hiS :=
      match I.hi with
      | none => "∞"
      | some r => Expr.toString (ofRat r)
    s!"{ls}{loS}, {hiS}{rs}"

/--
  Pretty-print a solve result:
  * `all` → `ℝ`
  * empty matrix → `∅`
  * n×1 of equations → `x = …, y = …`
  * n×2 / n×4 interval matrix → union of intervals
  * 1×n root row → `{a, b, …}`
  * otherwise default `Expr.toString`
-/
def prettySolution (e : Expr) : String :=
  match e with
  | var name =>
    if name == "all" || name == "ℝ" || name == "R" then "ℝ"
    else Expr.toString e
  | mat rows =>
    let nr := Mat.nrows rows
    let nc := Mat.ncols rows
    if nr == 1 && nc == 0 then "∅"
    else if nr == 0 then "∅"
    else if nc == 1 && nr ≥ 1 && rows.all (fun r =>
        match r[0]! with | eq _ _ => true | _ => false) then
      -- Named system solution
      let parts := rows.toList.map fun r => Expr.toString r[0]!
      String.intercalate ", " parts
    else if nc == 4 && nr ≥ 1 then
      -- Interval set (n×4: lo, hi, loClosed, hiClosed)
      let parsed := rows.toList.filterMap parseIntervalRow?
      if parsed.length == nr then
        match RealInterval.mergeAll parsed with
        | [] => "∅"
        | [I] =>
          if I.lo.isNone && I.hi.isNone then "ℝ"
          else formatInterval I
        | Is => String.intercalate " ∪ " (Is.map formatInterval)
      else Expr.toString e
    else if nr == 1 && nc ≥ 1 then
      -- 1×n root / value row → set notation
      let rs := rows[0]!.toList.map fun x => Expr.toString (simplify x)
      if rs.isEmpty then "∅" else s!"\{{String.intercalate ", " rs}}"
    else Expr.toString e
  | e => Expr.toString e

/--
  Solve univariate poly inequality `residual ? 0` in free var `v`.
  Returns:
  * `all` for the whole line
  * empty matrix for ∅
  * n×4 interval matrix `[lo, hi, loClosed, hiClosed]` after merge
    (Closed flags are 0/1; ±∞ for unbounded ends.)
-/
def solveInequality (residual : Expr) (kind : RelKind) (v : String) : Except String Expr :=
  let residual := simplify residual
  match asPolyIn? residual v with
  | none => throw "solve: inequality must be polynomial/rational in one variable"
  | some p =>
    let p := Poly.strip p
    if p.isZero then
      match kind with
      | .eq | .le | .ge => pure (var "all")
      | .lt | .gt => pure (Expr.mat #[#[]])
    else if p.deg == 0 then
      let c := Poly.coeff p 0
      let pos := c.num > 0
      match kind with
      | .eq => pure (Expr.mat #[#[]])
      | .lt => pure (if !pos && !c.isZero then var "all" else Expr.mat #[#[]])
      | .gt => pure (if pos then var "all" else Expr.mat #[#[]])
      | .le => pure (if !pos then var "all" else Expr.mat #[#[]])
      | .ge => pure (if pos || c.isZero then var "all" else Expr.mat #[#[]])
    else
      let rs := rootsPoly p
      let realRoots :=
        rs.filterMap fun r =>
          match simplify r with
          | const c =>
            match CplxConst.toRat? c with
            | some q => some q
            | none => none
          | _ => none
      let rootRats :=
        realRoots.eraseDups.toArray.qsort (fun a b =>
          RatConst.compare a b == .lt) |>.toList
      let n := rootRats.length
      let openSegs : List (Option RatConst × Option RatConst) :=
        if n == 0 then [(none, none)]
        else
          let left := (none, some rootRats[0]!)
          let right := (some rootRats[n - 1]!, none)
          let mids :=
            (List.range (n - 1)).map fun i =>
              (some rootRats[i]!, some rootRats[i + 1]!)
          left :: mids ++ [right]
      let closedEnds := kind == .le || kind == .ge
      if kind == .eq then
        let pts : List RealInterval :=
          rootRats.map fun r =>
            { lo := some r, hi := some r, loClosed := true, hiClosed := true }
        pure (RealInterval.toExpr pts)
      else
        let mutIs : List RealInterval :=
          Id.run do
            let mut acc : List RealInterval := []
            for (lo, hi) in openSegs do
              let t := midPoint lo hi
              match polySignAt p t with
              | none => pure ()
              | some pos =>
                let ok :=
                  (pos && (kind == .gt || kind == .ge))
                    || (!pos && (kind == .lt || kind == .le))
                if ok then
                  -- Finite ends: open for strict, closed for ≤/≥
                  let loC :=
                    match lo with
                    | none => false  -- −∞ always open
                    | some _ => closedEnds
                  let hiC :=
                    match hi with
                    | none => false
                    | some _ => closedEnds
                  acc := acc ++
                    [{ lo := lo, hi := hi, loClosed := loC, hiClosed := hiC }]
            -- Isolated roots for non-strict (sign zero, not interior of a segment)
            if closedEnds then
              for r in rootRats do
                let covered := acc.any (fun I => I.containsRat r)
                if !covered then
                  acc := acc ++
                    [{ lo := some r, hi := some r, loClosed := true, hiClosed := true }]
            pure acc
        pure (RealInterval.toExpr mutIs)

/-- Dispatch a single relation or residual for solve. -/
def solveRelation (e : Expr) (v : String) : Except String Expr :=
  match relationToResidual e with
  | some (.eq, r) => solveScalarExpr? r v
  | some (.lt, r) => solveInequality r .lt v
  | some (.le, r) => solveInequality r .le v
  | some (.gt, r) => solveInequality r .gt v
  | some (.ge, r) => solveInequality r .ge v
  | none =>
    -- bare expression = 0
    solveScalarExpr? e v

/-- Extract `vᵢ ↦ val` from a named system solution matrix. -/
def asNamedSolution? (e : Expr) : Option (List (String × Expr)) :=
  match asMat? e with
  | none => none
  | some rows =>
    if Mat.ncols rows != 1 then none
    else
      Id.run do
        let mut out : List (String × Expr) := []
        for i in [:Mat.nrows rows] do
          match rows[i]![0]! with
          | eq (var name) val => out := out ++ [(name, simplify val)]
          | _ => return none
        pure (some out)

/-- Look up a binding in a named solution. -/
def namedGet? (e : Expr) (v : String) : Option Expr :=
  match asNamedSolution? e with
  | none => none
  | some pairs =>
    match pairs.find? (fun p => p.1 == v) with
    | some (_, val) => some val
    | none => none

end Taschenrechner
