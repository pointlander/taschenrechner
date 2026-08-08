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

/-- Symbolic expression tree. -/
inductive Expr where
  | const : RatConst → Expr
  | var   : String → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | pow   : Expr → Expr → Expr
  | sin   : Expr → Expr
  | cos   : Expr → Expr
  | tan   : Expr → Expr
  | exp   : Expr → Expr
  | ln    : Expr → Expr
  deriving Repr, Inhabited

namespace Expr

def zero : Expr := const .zero
def one  : Expr := const .one
def negOne : Expr := const .negOne

def ofInt (n : Int) : Expr := const (RatConst.ofInt n)
def ofNat (n : Nat) : Expr := ofInt n

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
  | sin e | cos e | tan e | exp e | ln e => freeVars e

/-- Whether `v` occurs free in the expression. -/
partial def dependsOn (e : Expr) (v : String) : Bool :=
  match e with
  | const _ => false
  | var name => name == v
  | add a b | mul a b | pow a b => dependsOn a v || dependsOn b v
  | sin a | cos a | tan a | exp a | ln a => dependsOn a v

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
  | _, _ => false

instance : BEq Expr where beq := beq

/-- Pretty-printer with minimal parentheses. -/
partial def toString : Expr → String
  | const r => RatConst.toString r
  | var v => v
  | add a b =>
    let bs := match b with
      | mul (const r) e =>
        if r.isNegOne then s!" - {toString e}"
        else if r.num < 0 then
          s!" - {toString (mul (const (RatConst.neg r)) e)}"
        else s!" + {toString b}"
      | const r =>
        if r.num < 0 then s!" - {RatConst.toString (RatConst.neg r)}"
        else s!" + {toString b}"
      | _ => s!" + {toString b}"
    s!"{toString a}{bs}"
  | mul a b =>
    match a, b with
    | const r, e =>
      if r.isNegOne then s!"-({toString e})"
      else if r.isOne then toString e
      else s!"{toString a}·{parenMul e}"
    | _, _ => s!"{parenMul a}·{parenMul b}"
  | pow a b => s!"{parenPow a}^{parenPow b}"
  | sin e => s!"sin({toString e})"
  | cos e => s!"cos({toString e})"
  | tan e => s!"tan({toString e})"
  | exp e => s!"exp({toString e})"
  | ln e => s!"ln({toString e})"
where
  parenMul : Expr → String
    | e@(add _ _) => s!"({toString e})"
    | e => toString e
  parenPow : Expr → String
    | e@(add _ _) | e@(mul _ _) | e@(pow _ _) => s!"({toString e})"
    | e => toString e

instance : ToString Expr where
  toString := toString

end Expr

/-- Square root as a power. -/
def sqrt (e : Expr) : Expr := .pow e (.const ⟨1, 2⟩)

end Taschenrechner
