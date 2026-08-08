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

def toString (r : RatConst) : String :=
  let r := normalize r
  if r.den == 1 then s!"{r.num}"
  else if r.num < 0 then s!"-{-r.num}/{r.den}"
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
  | exp   : Expr → Expr
  | ln    : Expr → Expr
  | atan  : Expr → Expr
  | re    : Expr → Expr
  | im    : Expr → Expr
  | conj  : Expr → Expr
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
  | add a b | mul a b | pow a b => (freeVars a ++ freeVars b).eraseDups
  | sin e | cos e | tan e | exp e | ln e | atan e | re e | im e | conj e => freeVars e
  | mat rows =>
    rows.toList.foldl (fun acc row =>
      row.toList.foldl (fun acc e => (acc ++ freeVars e).eraseDups) acc) []

/-- Whether `v` occurs free in the expression. -/
partial def dependsOn (e : Expr) (v : String) : Bool :=
  match e with
  | const _ => false
  | var name => name == v
  | add a b | mul a b | pow a b => dependsOn a v || dependsOn b v
  | sin a | cos a | tan a | exp a | ln a | atan a | re a | im a | conj a => dependsOn a v
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
  | exp a, exp b => beq a b
  | ln a, ln b => beq a b
  | atan a, atan b => beq a b
  | re a, re b => beq a b
  | im a, im b => beq a b
  | conj a, conj b => beq a b
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

/-- Pretty-printer with minimal parentheses. -/
partial def toString : Expr → String
  | const c => CplxConst.toString c
  | var v => v
  | add a b =>
    let bs := match b with
      | mul (const r) e =>
        if r.isNegOne then s!" - {toString e}"
        else if r.isReal && r.re.num < 0 then
          s!" - {toString (mul (const (CplxConst.neg r)) e)}"
        else s!" + {toString b}"
      | const r =>
        if r.isReal && r.re.num < 0 then
          s!" - {CplxConst.toString (CplxConst.neg r)}"
        else if !r.isReal && r.re.isZero && r.im.num < 0 then
          s!" - {CplxConst.toString (CplxConst.neg r)}"
        else s!" + {toString b}"
      | _ => s!" + {toString b}"
    s!"{toString a}{bs}"
  | mul a b =>
    match a, b with
    | const r, e =>
      if r.isNegOne then s!"-({toString e})"
      else if r.isOne then toString e
      else if r.isPureI then s!"i·{parenMul e}"
      else s!"{toString a}·{parenMul e}"
    | _, _ => s!"{parenMul a}·{parenMul b}"
  | pow a b => s!"{parenPow a}^{parenPow b}"
  | sin e => s!"sin({toString e})"
  | cos e => s!"cos({toString e})"
  | tan e => s!"tan({toString e})"
  | exp e => s!"exp({toString e})"
  | ln e => s!"ln({toString e})"
  | atan e => s!"atan({toString e})"
  | re e => s!"re({toString e})"
  | im e => s!"im({toString e})"
  | conj e => s!"conj({toString e})"
  | mat rows =>
    let rowStrs := rows.toList.map fun row =>
      String.intercalate ", " (row.toList.map toString)
    s!"[{String.intercalate "; " rowStrs}]"
where
  parenMul : Expr → String
    | e@(add _ _) => s!"({toString e})"
    | e@(mat _) => s!"({toString e})"
    | e => toString e
  parenPow : Expr → String
    | e@(add _ _) | e@(mul _ _) | e@(pow _ _) | e@(mat _) => s!"({toString e})"
    | e => toString e

instance : ToString Expr where
  toString := toString

end Expr

/-- Square root as a power. -/
def sqrt (e : Expr) : Expr := .pow e (.const (CplxConst.ofRat ⟨1, 2⟩))

end Taschenrechner
