/-
  Symbolic expression AST for the Taschenrechner CAS.
-/
namespace Taschenrechner

/-- Exact rational constant `num / den` with `den > 0`. -/
structure RatConst where
  num : Int
  den : Nat
  deriving DecidableEq, Repr, Inhabited

namespace RatConst

def ofInt (n : Int) : RatConst := ⟨n, 1⟩

def zero : RatConst := ⟨0, 1⟩
def one  : RatConst := ⟨1, 1⟩
def negOne : RatConst := ⟨-1, 1⟩

def isZero (r : RatConst) : Bool := r.num == 0
def isOne  (r : RatConst) : Bool := r.num == r.den && r.num != 0
def isNegOne (r : RatConst) : Bool := r.num == -((r.den : Int)) && r.den != 0

def normalize (r : RatConst) : RatConst :=
  if r.den == 0 then ⟨0, 1⟩
  else
    let g := Nat.gcd r.num.natAbs r.den
    let n := r.num / (g : Int)
    let d := r.den / g
    ⟨n, d⟩

def compare (a b : RatConst) : Ordering :=
  let a := normalize a; let b := normalize b
  let lhs := a.num * (b.den : Int)
  let rhs := b.num * (a.den : Int)
  if lhs < rhs then .lt else if lhs > rhs then .gt else .eq

def add (a b : RatConst) : RatConst :=
  normalize ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

def mul (a b : RatConst) : RatConst :=
  normalize ⟨a.num * b.num, a.den * b.den⟩

def neg (a : RatConst) : RatConst := ⟨-a.num, a.den⟩

def sub (a b : RatConst) : RatConst := add a (neg b)

def inv (a : RatConst) : Option RatConst :=
  if a.num == 0 then none
  else
    if a.num > 0 then some (normalize ⟨(a.den : Int), a.num.natAbs⟩)
    else some (normalize ⟨-((a.den : Int)), a.num.natAbs⟩)

def div (a b : RatConst) : Option RatConst :=
  match inv b with
  | some b' => some (mul a b')
  | none => none

def powNat (a : RatConst) (k : Nat) : RatConst :=
  match k with
  | 0 => one
  | k'+1 => mul (powNat a k') a

/-- Exact integer `n`-th root of a natural, if it is a perfect power. -/
def natNthRoot? (n k : Nat) : Option Nat :=
  if n == 0 then none
  else if k == 0 then some 0
  else if k == 1 || n == 1 then some k
  else
    Id.run do
      let mut i : Nat := 1
      while i ≤ k do
        let p := Nat.pow i n
        if p == k then return some i
        if p > k then return none
        i := i + 1
      none

/-- Exact rational `n`-th root, if it exists in ℚ. Odd `n` allows a negative radicand. -/
def nthRoot? (r : RatConst) (n : Nat) : Option RatConst :=
  let r := normalize r
  if n == 0 then none
  else if n == 1 then some r
  else if r.isZero then some zero
  else
    let signNeg := r.num < 0
    if signNeg && n % 2 == 0 then none
    else
      let mag := if signNeg then neg r else r
      match natNthRoot? n mag.num.natAbs, natNthRoot? n mag.den with
      | some a, some b =>
        if b == 0 then none
        else
          let s := normalize ⟨(a : Int), b⟩
          some (if signNeg then neg s else s)
      | _, _ => none

def cbrt? (r : RatConst) : Option RatConst := nthRoot? r 3

def powInt (a : RatConst) (n : Int) : Option RatConst :=
  if n == 0 then some one
  else if a.isZero then
    if n > 0 then some zero else none
  else if n > 0 then
    some (powNat a n.toNat)
  else
    match inv a with
    | none => none
    | some a' => some (powNat a' n.natAbs)

/-- Count factors of prime `p` in `n` (n > 0). -/
partial def factorCount (n p : Nat) : Nat :=
  if n == 0 || p ≤ 1 then 0
  else if n % p == 0 then 1 + factorCount (n / p) p
  else 0

/-- Remove all factors of `p` from `n`. -/
partial def stripPrime (n p : Nat) : Nat :=
  if n == 0 || p ≤ 1 then n
  else if n % p == 0 then stripPrime (n / p) p
  else n

/-- Zero-pad digit list on the left to width `n`. -/
partial def padLeftZeros (ds : List Char) (n : Nat) : List Char :=
  if ds.length ≥ n then ds else padLeftZeros ('0' :: ds) n

/-- Strip trailing `'0'` from a digit list. -/
partial def rstripZeros (ds : List Char) : List Char :=
  match ds.reverse with
  | [] => ['0']
  | '0' :: rest => rstripZeros rest.reverse
  | _ => if ds.isEmpty then ['0'] else ds

/--
  Decimal rendering when the denominator's primes are only 2 and/or 5
  (e.g. 1/2 → `0.5`, 3/4 → `0.75`, 1/3 → none).
-/
def toDecimalString? (r : RatConst) : Option String :=
  let r := normalize r
  if r.den == 1 then none  -- prefer plain integer form
  else
    let d := r.den
    let a := factorCount d 2
    let b := factorCount d 5
    let rest := stripPrime (stripPrime d 2) 5
    if rest != 1 then none
    else
      let k := max a b
      let scale2 := Nat.pow 2 (k - a)
      let scale5 := Nat.pow 5 (k - b)
      let mag : Nat := r.num.natAbs * scale2 * scale5
      let sign := if r.num < 0 then "-" else ""
      if k == 0 then some s!"{sign}{mag}"
      else
        let tenK := Nat.pow 10 k
        let whole := mag / tenK
        let frac := mag % tenK
        let fracCs := rstripZeros (padLeftZeros (toString frac).toList k)
        let fracS := String.ofList fracCs
        if fracS == "0" then some s!"{sign}{whole}"
        else some s!"{sign}{whole}.{fracS}"

def toString (r : RatConst) : String :=
  let r := normalize r
  if r.den == 1 then s!"{r.num}"
  else
    match toDecimalString? r with
    | some s => s
    | none =>
      if r.num < 0 then s!"-{-r.num}/{r.den}"
      else s!"{r.num}/{r.den}"

instance : ToString RatConst where
  toString := toString

instance : BEq RatConst where
  beq a b :=
    let a := normalize a
    let b := normalize b
    a.num == b.num && a.den == b.den

instance : Add RatConst where add := add
instance : Mul RatConst where mul := mul
instance : Neg RatConst where neg := neg
instance : Sub RatConst where sub := sub

instance : OfNat RatConst n where
  ofNat := ofInt n

end RatConst

/-! ### Complex constants over ℚ(i) -/

/-- Exact complex constant `re + im·i` with rational real/imag parts. -/
structure CplxConst where
  re : RatConst
  im : RatConst
  deriving DecidableEq, Repr, Inhabited

namespace CplxConst

def ofRat (r : RatConst) : CplxConst := ⟨r, .zero⟩
def ofInt (n : Int) : CplxConst := ofRat (RatConst.ofInt n)
def zero : CplxConst := ⟨.zero, .zero⟩
def one  : CplxConst := ⟨.one, .zero⟩
def negOne : CplxConst := ⟨.negOne, .zero⟩
/-- The imaginary unit `i`. -/
def I : CplxConst := ⟨.zero, .one⟩

def isZero (c : CplxConst) : Bool := c.re.isZero && c.im.isZero
def isOne  (c : CplxConst) : Bool := c.re.isOne && c.im.isZero
def isNegOne (c : CplxConst) : Bool := c.re.isNegOne && c.im.isZero
def isReal (c : CplxConst) : Bool := c.im.isZero
def isImag (c : CplxConst) : Bool := c.re.isZero && !c.im.isZero
def isPureI (c : CplxConst) : Bool := c.re.isZero && c.im.isOne

def toRat? (c : CplxConst) : Option RatConst :=
  if c.im.isZero then some c.re else none

def normalize (c : CplxConst) : CplxConst :=
  ⟨RatConst.normalize c.re, RatConst.normalize c.im⟩

def add (a b : CplxConst) : CplxConst :=
  normalize ⟨a.re + b.re, a.im + b.im⟩

def neg (a : CplxConst) : CplxConst := ⟨RatConst.neg a.re, RatConst.neg a.im⟩

def sub (a b : CplxConst) : CplxConst := add a (neg b)

def mul (a b : CplxConst) : CplxConst :=
  -- (a+bi)(c+di) = (ac-bd) + (ad+bc)i
  normalize ⟨
    a.re * b.re - a.im * b.im,
    a.re * b.im + a.im * b.re
  ⟩

def conj (a : CplxConst) : CplxConst := ⟨a.re, RatConst.neg a.im⟩

/-- `|z|² = re² + im²` (always real, non-negative). -/
def absSq (a : CplxConst) : RatConst :=
  a.re * a.re + a.im * a.im

def inv (a : CplxConst) : Option CplxConst :=
  let n := absSq a
  if n.isZero then none
  else
    match RatConst.inv n with
    | none => none
    | some invN =>
      -- 1/z = conj(z) / |z|²
      some (normalize ⟨a.re * invN, RatConst.neg a.im * invN⟩)

def div (a b : CplxConst) : Option CplxConst :=
  match inv b with
  | some b' => some (mul a b')
  | none => none

def powNat (a : CplxConst) (k : Nat) : CplxConst :=
  match k with
  | 0 => one
  | k'+1 => mul (powNat a k') a

def powInt (a : CplxConst) (n : Int) : Option CplxConst :=
  if n == 0 then some one
  else if a.isZero then
    if n > 0 then some zero else none
  else if n > 0 then
    some (powNat a n.toNat)
  else
    match inv a with
    | none => none
    | some a' => some (powNat a' n.natAbs)

def toString (c : CplxConst) : String :=
  let c := normalize c
  if c.im.isZero then RatConst.toString c.re
  else if c.re.isZero then
    if c.im.isOne then "i"
    else if c.im.isNegOne then "-i"
    else s!"{RatConst.toString c.im}*i"
  else
    let imPart :=
      if c.im.isOne then "+i"
      else if c.im.isNegOne then "-i"
      else if c.im.num < 0 then s!"-{RatConst.toString (RatConst.neg c.im)}*i"
      else s!"+{RatConst.toString c.im}*i"
    s!"{RatConst.toString c.re}{imPart}"

instance : ToString CplxConst where
  toString := toString

instance : BEq CplxConst where
  beq a b :=
    let a := normalize a
    let b := normalize b
    a.re == b.re && a.im == b.im

instance : Add CplxConst where add := add
instance : Mul CplxConst where mul := mul
instance : Neg CplxConst where neg := neg
instance : Sub CplxConst where sub := sub

instance : OfNat CplxConst n where
  ofNat := ofInt n

end CplxConst

/-- Symbolic expression tree. Constants are complex rationals `ℚ(i)`. -/
inductive Expr where
  | const : CplxConst → Expr
  | var   : String → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | pow   : Expr → Expr → Expr
  | sin   : Expr → Expr
  | cos   : Expr → Expr
  | tan   : Expr → Expr
  | sinh  : Expr → Expr
  | cosh  : Expr → Expr
  | tanh  : Expr → Expr
  | exp   : Expr → Expr
  | ln    : Expr → Expr
  | atan  : Expr → Expr
  | asin  : Expr → Expr
  | acos  : Expr → Expr
  | sec   : Expr → Expr
  | csc   : Expr → Expr
  | cot   : Expr → Expr
  | factorial : Expr → Expr
  | gamma : Expr → Expr
  | floor : Expr → Expr
  /-- `if c then t else e`. Conditions are relations (`=`, `<`, `≤`). -/
  | ite   : Expr → Expr → Expr → Expr
  | abs   : Expr → Expr
  | re    : Expr → Expr
  | im    : Expr → Expr
  | conj  : Expr → Expr
  /-- Equation `lhs = rhs` (for `solve` and display). -/
  | eq    : Expr → Expr → Expr
  /-- Strict inequality `lhs < rhs`. -/
  | lt    : Expr → Expr → Expr
  /-- Non-strict inequality `lhs ≤ rhs`. -/
  | le    : Expr → Expr → Expr
  /-- Rectangular matrix; rows are arrays of equal length. -/
  | mat   : Array (Array Expr) → Expr
  deriving Repr, Inhabited

namespace Expr

def zero : Expr := const .zero
def one  : Expr := const .one
def negOne : Expr := const .negOne
/-- Imaginary unit as an expression. -/
def I : Expr := const .I

def ofRat (r : RatConst) : Expr := const (CplxConst.ofRat r)
def ofInt (n : Int) : Expr := const (CplxConst.ofInt n)
def ofNat (n : Nat) : Expr := ofInt n
def ofCplx (c : CplxConst) : Expr := const c

/-- `n!` as a natural. -/
def factNat : Nat → Nat
  | 0 => 1
  | n'+1 => (n'+1) * factNat n'

/-- Nonnegative integer constant, if any. -/
def asNat? : Expr → Option Nat
  | const c =>
    match CplxConst.toRat? c with
    | some q =>
      if q.den == 1 && q.num ≥ 0 then some q.num.toNat else none
    | none => none
  | _ => none

def neg (e : Expr) : Expr := mul negOne e

def sub (a b : Expr) : Expr := add a (neg b)

/-- `a / b` as `a * b^(-1)`. -/
def div (a b : Expr) : Expr := mul a (pow b negOne)

instance : OfNat Expr n where
  ofNat := ofNat n

instance : Add Expr where add := add
instance : Mul Expr where mul := mul
instance : Neg Expr where neg := neg
instance : Sub Expr where sub := sub
instance : Div Expr where div := div
instance : HPow Expr Expr Expr where hPow := pow

/-- Default independent variable. -/
def x : Expr := var "x"
def y : Expr := var "y"
def z : Expr := var "z"

/-- Free variables appearing in an expression. -/
partial def freeVars : Expr → List String
  | const _ => []
  | var v => [v]
  | add a b | mul a b | pow a b | eq a b | lt a b | le a b =>
      (freeVars a ++ freeVars b).eraseDups
  | ite c t e => (freeVars c ++ freeVars t ++ freeVars e).eraseDups
  | sin e | cos e | tan e | sinh e | cosh e | tanh e
  | exp e | ln e | atan e | asin e | acos e | sec e | csc e | cot e
  | factorial e | gamma e | floor e | abs e | re e | im e | conj e =>
      freeVars e
  | mat rows =>
    rows.toList.foldl (fun acc row =>
      row.toList.foldl (fun acc e => (acc ++ freeVars e).eraseDups) acc) []

/-- Whether `v` occurs free in the expression. -/
partial def dependsOn (e : Expr) (v : String) : Bool :=
  match e with
  | const _ => false
  | var name => name == v
  | add a b | mul a b | pow a b | eq a b | lt a b | le a b =>
      dependsOn a v || dependsOn b v
  | ite c t e => dependsOn c v || dependsOn t v || dependsOn e v
  | sin a | cos a | tan a | sinh a | cosh a | tanh a
  | exp a | ln a | atan a | asin a | acos a | sec a | csc a | cot a
  | factorial a | gamma a | floor a | abs a | re a | im a | conj a =>
      dependsOn a v
  | mat rows => rows.any (fun row => row.any (fun e => dependsOn e v))

/-- Structural equality (not algebraic). -/
partial def beq : Expr → Expr → Bool
  | const a, const b => a == b
  | var a, var b => a == b
  | add a1 b1, add a2 b2 => beq a1 a2 && beq b1 b2
  | mul a1 b1, mul a2 b2 => beq a1 a2 && beq b1 b2
  | pow a1 b1, pow a2 b2 => beq a1 a2 && beq b1 b2
  | sin a, sin b => beq a b
  | cos a, cos b => beq a b
  | tan a, tan b => beq a b
  | sinh a, sinh b => beq a b
  | cosh a, cosh b => beq a b
  | tanh a, tanh b => beq a b
  | exp a, exp b => beq a b
  | ln a, ln b => beq a b
  | atan a, atan b => beq a b
  | asin a, asin b => beq a b
  | acos a, acos b => beq a b
  | sec a, sec b => beq a b
  | csc a, csc b => beq a b
  | cot a, cot b => beq a b
  | factorial a, factorial b => beq a b
  | gamma a, gamma b => beq a b
  | floor a, floor b => beq a b
  | ite c1 t1 e1, ite c2 t2 e2 => beq c1 c2 && beq t1 t2 && beq e1 e2
  | abs a, abs b => beq a b
  | re a, re b => beq a b
  | im a, im b => beq a b
  | conj a, conj b => beq a b
  | eq a1 b1, eq a2 b2 => beq a1 a2 && beq b1 b2
  | lt a1 b1, lt a2 b2 => beq a1 a2 && beq b1 b2
  | le a1 b1, le a2 b2 => beq a1 a2 && beq b1 b2
  | mat a, mat b =>
    a.size == b.size &&
      Id.run do
        for i in [:a.size] do
          let ra := a[i]!; let rb := b[i]!
          if ra.size != rb.size then return false
          for j in [:ra.size] do
            if !(beq ra[j]! rb[j]!) then return false
        pure true
  | _, _ => false

instance : BEq Expr where beq := beq

/-! ### Substitution -/

/-- Replace free occurrences of variable `v` by `val`. -/
partial def subst (e : Expr) (v : String) (val : Expr) : Expr :=
  match e with
  | const c => const c
  | var name => if name == v then val else var name
  | add a b => add (subst a v val) (subst b v val)
  | mul a b => mul (subst a v val) (subst b v val)
  | pow a b => pow (subst a v val) (subst b v val)
  | sin a => sin (subst a v val)
  | cos a => cos (subst a v val)
  | tan a => tan (subst a v val)
  | sinh a => sinh (subst a v val)
  | cosh a => cosh (subst a v val)
  | tanh a => tanh (subst a v val)
  | exp a => exp (subst a v val)
  | ln a => ln (subst a v val)
  | atan a => atan (subst a v val)
  | asin a => asin (subst a v val)
  | acos a => acos (subst a v val)
  | sec a => sec (subst a v val)
  | csc a => csc (subst a v val)
  | cot a => cot (subst a v val)
  | factorial a => factorial (subst a v val)
  | gamma a => gamma (subst a v val)
  | floor a => floor (subst a v val)
  | ite c t e => ite (subst c v val) (subst t v val) (subst e v val)
  | abs a => abs (subst a v val)
  | re a => re (subst a v val)
  | im a => im (subst a v val)
  | conj a => conj (subst a v val)
  | eq a b => eq (subst a v val) (subst b v val)
  | lt a b => lt (subst a v val) (subst b v val)
  | le a b => le (subst a v val) (subst b v val)
  | mat rows => mat (rows.map fun row => row.map fun cell => subst cell v val)

/-- If `e` is an equation `lhs = rhs`, return both sides. -/
def asEquation? : Expr → Option (Expr × Expr)
  | eq a b => some (a, b)
  | _ => none

/-- Relation kind for equations and inequalities. -/
inductive RelKind where
  | eq | lt | le | gt | ge
  deriving Repr, BEq, DecidableEq, Inhabited

/-- If `e` is a relation, return kind and sides (gt/ge normalized to lt/le swapped). -/
def asRelation? : Expr → Option (RelKind × Expr × Expr)
  | eq a b => some (.eq, a, b)
  | lt a b => some (.lt, a, b)
  | le a b => some (.le, a, b)
  | _ => none

/-- Convert equation to `lhs - rhs` (for solving); leave non-equations unchanged. -/
def equationToZero (e : Expr) : Expr :=
  match e with
  | eq a b => sub a b
  | e => e

/-- Convert any comparison to a residual `lhs - rhs` with a relation kind. -/
def relationToResidual : Expr → Option (RelKind × Expr)
  | eq a b => some (.eq, sub a b)
  | lt a b => some (.lt, sub a b)
  | le a b => some (.le, sub a b)
  | _ => none

/-- Apply a list of substitutions left-to-right. -/
def substMany (e : Expr) (σ : List (String × Expr)) : Expr :=
  σ.foldl (fun acc pair => subst acc pair.1 pair.2) e

/-! ### Pretty-printing (fraction-aware, degree-sorted, √ / ∞) -/

/-- Local product flatten (no dependency on Simplify). -/
partial def flattenMulLocal : Expr → List Expr
  | mul a b => flattenMulLocal a ++ flattenMulLocal b
  | e => [e]

/-- Local sum flatten. -/
partial def flattenAddLocal : Expr → List Expr
  | add a b => flattenAddLocal a ++ flattenAddLocal b
  | e => [e]

/-- Infinity-like variable names. -/
def isInfName (v : String) : Bool :=
  let n := v.toLower
  n == "oo" || n == "inf" || n == "infty" || n == "infinity" || v == "∞"

/-- Reserved name for the real constant π. -/
def isPiName (v : String) : Bool :=
  v == "π" || v.toLower == "pi"

/-- Canonical π expression. -/
def piE : Expr := var "π"

/-- `e = q·π` for a rational `q` (includes `π`, `-π`, `π/2`, `2π`, …). -/
def asRatPi? : Expr → Option RatConst
  | var v => if isPiName v then some RatConst.one else none
  | mul (const c) (var v) =>
    if isPiName v then CplxConst.toRat? c else none
  | mul (var v) (const c) =>
    if isPiName v then CplxConst.toRat? c else none
  | mul (const c) e =>
    if c.isReal then
      match asRatPi? e with
      | some q => some (c.re * q)
      | none => none
    else none
  | _ => none

/-- Prefer free var `x`, else `t`, else first free var (for degree sorting). -/
def printPrimaryVar (e : Expr) : String :=
  if dependsOn e "x" then "x"
  else if dependsOn e "t" then "t"
  else match freeVars e with
    | v :: _ => v
    | [] => "x"

/-- Total degree of a monomial-like term in free variable `v` (heuristic). -/
partial def termDegree (e : Expr) (v : String) : Int :=
  match e with
  | const _ => 0
  | var name => if name == v then 1 else 0
  | mul a b => termDegree a v + termDegree b v
  | pow base (const r) =>
    match CplxConst.toRat? r with
    | some q =>
      if q.den == 1 then termDegree base v * q.num
      else if q == ⟨1, 2⟩ || q == ⟨-1, 2⟩ then termDegree base v  -- treat √ as deg 1 of base
      else termDegree base v
    | none => termDegree base v
  | pow base _ => termDegree base v
  | sin e | cos e | tan e | sinh e | cosh e | tanh e
  | exp e | ln e | atan e | asin e | acos e | sec e | csc e | cot e
  | factorial e | gamma e | floor e | abs e | re e | im e | conj e =>
      -- transcendental: sort after polynomials of same “priority”
      100 + termDegree e v
  | ite c t e => max (termDegree c v) (max (termDegree t v) (termDegree e v))
  | eq a b | lt a b | le a b => max (termDegree a v) (termDegree b v)
  | mat _ => 0
  | add _ _ => 0

/--
  Split a product into constant coefficient, numerator factors, and
  denominator factors (from negative integer powers).
-/
partial def splitProduct (e : Expr) : CplxConst × List Expr × List Expr :=
  let rec go (fs : List Expr) (c : CplxConst) (nums dens : List Expr) :
      CplxConst × List Expr × List Expr :=
    match fs with
    | [] => (c, nums, dens)
    | f :: rest =>
      match f with
      | const k => go rest (c * k) nums dens
      | pow base (const r) =>
        match CplxConst.toRat? r with
        | some q =>
          if q.den == 1 then
            let k := q.num
            if k == 0 then go rest c nums dens
            else if k > 0 then
              let t := if k == 1 then base else pow base (ofInt k)
              go rest c (nums ++ [t]) dens
            else
              let t := if k == -1 then base else pow base (ofInt (-k))
              go rest c nums (dens ++ [t])
          else if q == ⟨-1, 2⟩ then
            -- 1/√base
            go rest c nums (dens ++ [pow base (const (CplxConst.ofRat ⟨1, 2⟩))])
          else go rest c (nums ++ [f]) dens
        | none => go rest c (nums ++ [f]) dens
      | _ => go rest c (nums ++ [f]) dens
  go (flattenMulLocal e) CplxConst.one [] []

/-- Unicode superscript for small natural exponents. -/
def superscriptNat : Nat → String
  | 0 => "⁰"
  | 1 => "¹"
  | 2 => "²"
  | 3 => "³"
  | 4 => "⁴"
  | 5 => "⁵"
  | 6 => "⁶"
  | 7 => "⁷"
  | 8 => "⁸"
  | 9 => "⁹"
  | n =>
    if n < 10 then "?"
    else superscriptNat (n / 10) ++ superscriptNat (n % 10)

/-- Pretty-printer with fractions, √, degree-sorted sums, and ∞. -/
partial def toString : Expr → String
  | const c => CplxConst.toString c
  | var v =>
    if isInfName v then "∞"
    else if isPiName v then "π"
    else v
  | add a b => prettySum (add a b)
  | mul a b => prettyProduct (mul a b)
  | pow a b => prettyPow a b
  | sin e => s!"sin({toString e})"
  | cos e => s!"cos({toString e})"
  | tan e => s!"tan({toString e})"
  | sinh e => s!"sinh({toString e})"
  | cosh e => s!"cosh({toString e})"
  | tanh e => s!"tanh({toString e})"
  | exp e => s!"exp({toString e})"
  | ln e => s!"ln({toString e})"
  | atan e => s!"atan({toString e})"
  | asin e => s!"asin({toString e})"
  | acos e => s!"acos({toString e})"
  | sec e => s!"sec({toString e})"
  | csc e => s!"csc({toString e})"
  | cot e => s!"cot({toString e})"
  | factorial e =>
    match e with
    | const _ | var _ => s!"{toString e}!"
    | _ => s!"({toString e})!"
  | gamma e => s!"gamma({toString e})"
  | floor e => s!"floor({toString e})"
  | ite c t e => s!"if({toString c}, {toString t}, {toString e})"
  | abs e => s!"|{toString e}|"
  | re e => s!"re({toString e})"
  | im e => s!"im({toString e})"
  | conj e => s!"conj({toString e})"
  | eq a b => s!"{toString a} = {toString b}"
  | lt a b => s!"{toString a} < {toString b}"
  | le a b => s!"{toString a} ≤ {toString b}"
  | mat rows =>
    let rowStrs := rows.toList.map fun row =>
      String.intercalate ", " (row.toList.map toString)
    s!"[{String.intercalate "; " rowStrs}]"
where
  parenMul : Expr → String
    | e@(add _ _) => s!"({toString e})"
    | e@(eq _ _) | e@(lt _ _) | e@(le _ _) => s!"({toString e})"
    | e@(mat _) => s!"({toString e})"
    | e => toString e
  parenPow : Expr → String
    | e@(add _ _) | e@(mul _ _) | e@(pow _ _) | e@(eq _ _) | e@(lt _ _) | e@(le _ _)
    | e@(mat _) => s!"({toString e})"
    | e => toString e
  parenFrac : Expr → String
    | e@(add _ _) | e@(eq _ _) | e@(lt _ _) | e@(le _ _) => s!"({toString e})"
    | e => toString e
  parenSqrt : Expr → String
    | e@(add _ _) | e@(mul _ _) | e@(eq _ _) | e@(lt _ _) | e@(le _ _) => s!"({toString e})"
    | e => toString e
  /-- Format one summand with optional leading sign (`first` term has no leading +). -/
  formatSummand (first : Bool) (t : Expr) : String :=
    match t with
    | mul (const r) e =>
      if r.isNegOne then
        if first then s!"-{toString e}" else s!" - {toString e}"
      else if r.isReal && r.re.num < 0 then
        let body := toString (mul (const (CplxConst.neg r)) e)
        if first then s!"-{body}" else s!" - {body}"
      else if first then toString t
      else s!" + {toString t}"
    | const r =>
      if r.isReal && r.re.num < 0 then
        let s := CplxConst.toString (CplxConst.neg r)
        if first then s!"-{s}" else s!" - {s}"
      else if !r.isReal && r.re.isZero && r.im.num < 0 then
        let s := CplxConst.toString (CplxConst.neg r)
        if first then s!"-{s}" else s!" - {s}"
      else if first then toString t
      else s!" + {toString t}"
    | _ => if first then toString t else s!" + {toString t}"
  prettySum (e : Expr) : String :=
    let v := printPrimaryVar e
    let terms := flattenAddLocal e
    -- Degree descending (standard poly form: t² − 3t + 2)
    let terms := terms.toArray.qsort (fun a b =>
      let da := termDegree a v
      let db := termDegree b v
      if da != db then da > db
      else
        -- stable-ish: shorter string first
        (toString a).length < (toString b).length) |>.toList
    match terms with
    | [] => "0"
    | t :: ts =>
      ts.foldl (fun acc u => acc ++ formatSummand false u) (formatSummand true t)
  /-- Join product factors with middle-dot (no denominator). -/
  joinMul (coeff : CplxConst) (parts : List Expr) : String :=
    if coeff.isZero then "0"
    else
      let body :=
        match parts with
        | [] => ""
        | p :: ps =>
          ps.foldl (fun acc t => s!"{acc}·{parenMul t}") (parenMul p)
      if parts.isEmpty then
        CplxConst.toString coeff
      else if coeff.isOne then body
      else if coeff.isNegOne then s!"-{parenMul (foldMulParts parts)}"
      else if coeff.isPureI then s!"i·{body}"
      else s!"{CplxConst.toString coeff}·{body}"
  foldMulParts : List Expr → Expr
    | [] => one
    | p :: ps => ps.foldl mul p
  prettyProduct (e : Expr) : String :=
    -- (−1)·∞ → −∞
    match e with
    | mul (const r) (var v) =>
      if r.isNegOne && isInfName v then "-∞"
      else if r.isReal && r.re.num < 0 && isInfName v then "-∞"
      else defaultProd e
    | _ => defaultProd e
  defaultProd (e : Expr) : String :=
    let (c, nums, dens) := splitProduct e
    if dens.isEmpty then
      joinMul c nums
    else
      let numE :=
        if c.isOne && nums.isEmpty then one
        else if c.isOne then foldMulParts nums
        else if nums.isEmpty then const c
        else mul (const c) (foldMulParts nums)
      let denE := foldMulParts dens
      let numS :=
        if match numE with | const k => k.isOne | _ => false then "1"
        else parenFrac numE
      let denS := parenFrac denE
      s!"{numS}/{denS}"
  prettyPow (a b : Expr) : String :=
    match b with
    | const r =>
      match CplxConst.toRat? r with
      | some q =>
        if q == ⟨1, 2⟩ then
          s!"√{parenSqrt a}"
        else if q == ⟨-1, 2⟩ then
          s!"1/√{parenSqrt a}"
        else if q.den == 1 && q.num < 0 then
          let k := -q.num
          let den := if k == 1 then a else pow a (ofInt k)
          s!"1/{parenFrac den}"
        else if q.den == 1 && q.num == 0 then "1"
        else if q.den == 1 && q.num ≥ 2 && q.num ≤ 9 then
          -- x², x³, … for simple bases
          match a with
          | var _ | const _ => s!"{toString a}{superscriptNat q.num.toNat}"
          | _ => s!"{parenPow a}{superscriptNat q.num.toNat}"
        else if q.den == 1 && q.num == 1 then toString a
        else s!"{parenPow a}^{parenPow b}"
      | none => s!"{parenPow a}^{parenPow b}"
    | _ => s!"{parenPow a}^{parenPow b}"

instance : ToString Expr where
  toString := toString

end Expr

/-- Square root as a power. -/
def sqrt (e : Expr) : Expr := .pow e (.const (CplxConst.ofRat ⟨1, 2⟩))

end Taschenrechner
