/-
  Algebraic normal forms on top of `simplify` / `expand`.

  * `cancel`  — cancel common factors in products / quotients (integer powers)
  * `together`— put rational expressions in one variable over a common denominator
  * `normalForm` — simplify ∘ cancel ∘ together (default free var `"x"`)
  * `isZeroExpr` — stronger zero test for RREF pivots and verification
-/
import Taschenrechner.Simplify
import Taschenrechner.RatInt

namespace Taschenrechner.Expr

/-! ### Factor multiset (integer powers) -/

/-- Constant coefficient + list of (base, integer exponent). -/
structure Factorization where
  coeff : CplxConst
  factors : List (Expr × Int)
  deriving Repr, Inhabited

namespace Factorization

def one : Factorization := ⟨CplxConst.one, []⟩

def ofConst (c : CplxConst) : Factorization := ⟨c, []⟩

def mul (a b : Factorization) : Factorization :=
  let coeff := a.coeff * b.coeff
  let rec insert (base : Expr) (k : Int) : List (Expr × Int) → List (Expr × Int)
    | [] => if k == 0 then [] else [(base, k)]
    | (b, e) :: rest =>
      if b == base then
        let e' := e + k
        if e' == 0 then rest else (b, e') :: rest
      else (b, e) :: insert base k rest
  let factors := b.factors.foldl (fun acc pair => insert pair.1 pair.2 acc) a.factors
  ⟨coeff, factors.filter fun pair => pair.2 != 0⟩

def ofPow (base : Expr) (k : Int) : Factorization :=
  if k == 0 then one
  else ⟨CplxConst.one, [(base, k)]⟩

/-- Rebuild expression from factorization (sorted bases). -/
partial def toExpr (f : Factorization) : Expr :=
  let sorted := (f.factors.toArray.qsort fun a b => cmpExpr a.1 b.1 == .lt).toList
  let f := { f with factors := sorted }
  if f.coeff.isZero then zero
  else
    let parts : List Expr :=
      f.factors.map fun pair =>
        let base := pair.1
        let k := pair.2
        if k == 1 then base
        else if k == -1 then pow base (const CplxConst.negOne)
        else pow base (ofInt k)
    match parts with
    | [] => const f.coeff
    | p :: ps =>
      let body := ps.foldl (fun acc t => Expr.mul acc t) p
      if f.coeff.isOne then body
      else if f.coeff.isNegOne then Expr.neg body
      else Expr.mul (const f.coeff) body

end Factorization

/-- Factor an expression into constant × ∏ base^k (integer k only). -/
partial def factorize : Expr → Factorization
  | const c => Factorization.ofConst c
  | mul a b => Factorization.mul (factorize a) (factorize b)
  | pow base (const r) =>
    match CplxConst.toRat? r with
    | some q =>
      if q.den == 1 then
        let n := q.num
        let fb := factorize base
        -- (c * ∏ b_i^{e_i})^n = c^n * ∏ b_i^{e_i n}
        let coeff :=
          match CplxConst.powInt fb.coeff n with
          | some c => c
          | none => CplxConst.one
        let factors := fb.factors.map fun pair => (pair.1, pair.2 * n)
        { coeff, factors := factors.filter fun pair => pair.2 != 0 }
      else Factorization.ofPow (pow base (const r)) 1
    | none => Factorization.ofPow (pow base (const r)) 1
  | pow base e => Factorization.ofPow (pow base e) 1
  | e => Factorization.ofPow e 1

/-- Cancel common factors in products and quotients (`a/b` as `a·b⁻¹`). -/
partial def cancel1 : Expr → Expr
  | add a b => add (cancel1 a) (cancel1 b)
  | mul a b =>
    -- factorize whole product tree after canceling children
    let e := mul (cancel1 a) (cancel1 b)
    Factorization.toExpr (factorize e)
  | pow a b =>
    let a := cancel1 a
    let b := cancel1 b
    match b with
    | const r =>
      match CplxConst.toRat? r with
      | some q =>
        if q.den == 1 then
          Factorization.toExpr (factorize (pow a b))
        else pow a b
      | none => pow a b
    | _ => pow a b
  | sin e => sin (cancel1 e)
  | cos e => cos (cancel1 e)
  | tan e => tan (cancel1 e)
  | sinh e => sinh (cancel1 e)
  | cosh e => cosh (cancel1 e)
  | tanh e => tanh (cancel1 e)
  | exp e => exp (cancel1 e)
  | ln e => ln (cancel1 e)
  | atan e => atan (cancel1 e)
  | asin e => asin (cancel1 e)
  | acos e => acos (cancel1 e)
  | abs e => abs (cancel1 e)
  | re e => re (cancel1 e)
  | im e => im (cancel1 e)
  | conj e => conj (cancel1 e)
  | eq a b => eq (cancel1 a) (cancel1 b)
  | lt a b => lt (cancel1 a) (cancel1 b)
  | le a b => le (cancel1 a) (cancel1 b)
  | mat rows => mat (rows.map fun row => row.map cancel1)
  | e => e

/-- Prefer free var `"x"` when present; otherwise the first free variable. -/
def primaryVar (e : Expr) : String :=
  if dependsOn e "x" then "x"
  else match freeVars e with
    | v :: _ => v
    | [] => "x"

def cancel (e : Expr) : Expr :=
  let e0 := simplify (cancel1 (simplify e))
  -- When the expression is rational in the primary free var, cancel via poly GCD
  let v := primaryVar e0
  match RatFn.ofExpr? e0 v with
  | some r => simplify (RatFn.toExpr (RatFn.simplify r) v)
  | none => e0

/--
  Put a rational expression in free variable `v` over a common denominator
  (via `RatFn`). Falls back to cancel when not rational in `v`.
-/
def together (e : Expr) (v : String := "x") : Expr :=
  let e := simplify e
  match RatFn.ofExpr? e v with
  | some r =>
    -- ofExpr? already simplifies; rebuild canonical poly/poly form
    RatFn.toExpr (RatFn.simplify r) v
  | none =>
    -- try termwise: sum of rationals
    let terms := flattenAdd e
    let rec collect (ts : List Expr) (acc : Option RatFn) : Option RatFn :=
      match ts with
      | [] => acc
      | t :: rest =>
        match RatFn.ofExpr? t v with
        | none => none
        | some r =>
          let acc :=
            match acc with
            | none => some r
            | some a => some (RatFn.add a r)
          collect rest acc
    match collect terms none with
    | some r => RatFn.toExpr (RatFn.simplify r) v
    | none => cancel e

/--
  Full algebraic normal form:
  simplify → cancel → together (in `v`) → simplify.
-/
def normalForm (e : Expr) (v : String := "x") : Expr :=
  let e := simplify e
  let e := cancel e
  let e := together e v
  simplify e

/-- Stronger zero test for pivots / verification. -/
def isZeroExpr (e : Expr) (v : String := "x") : Bool :=
  let e0 := simplify e
  match e0 with
  | const c => c.isZero
  | _ =>
    if e0 == zero then true
    else
      let e1 := normalForm e0 v
      match e1 with
      | const c => c.isZero
      | _ =>
        e1 == zero ||
          match RatFn.ofExpr? e1 v with
          | some r => r.num.isZero
          | none =>
            -- expand and try again
            let e2 := simplify (expand e0)
            match e2 with
            | const c => c.isZero
            | _ =>
              match RatFn.ofExpr? e2 v with
              | some r => r.num.isZero
              | none => e2 == zero

/-- Algebraic equivalence via normal forms. -/
def equivNF (a b : Expr) (v : String := "x") : Bool :=
  let a := normalForm a v
  let b := normalForm b v
  a == b || isZeroExpr (sub a b) v

end Taschenrechner.Expr

namespace Taschenrechner

/-- Re-export under root for convenience. -/
def cancel (e : Expr) : Expr := Expr.cancel e
def together (e : Expr) (v : String := "x") : Expr := Expr.together e v
def normalForm (e : Expr) (v : String := "x") : Expr := Expr.normalForm e v
def isZeroExpr (e : Expr) (v : String := "x") : Bool := Expr.isZeroExpr e v
def equivNF (a b : Expr) (v : String := "x") : Bool := Expr.equivNF a b v

end Taschenrechner
