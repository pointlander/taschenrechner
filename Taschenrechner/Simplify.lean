/-
  Algebraic simplification toward a usable normal form.
-/
import Taschenrechner.Expr

namespace Taschenrechner.Expr

/-! ### Term collection helpers

We rewrite sums as lists of summands and products as lists of factors,
then reassociate, sort, and recombine. -/

partial def flattenAdd : Expr → List Expr
  | add a b => flattenAdd a ++ flattenAdd b
  | e => [e]

partial def flattenMul : Expr → List Expr
  | mul a b => flattenMul a ++ flattenMul b
  | e => [e]

/-- Ordering for canonical form (constants first, then vars, then compound). -/
partial def cmpExpr : Expr → Expr → Ordering
  | const a, const b =>
    if a.num < b.num then .lt
    else if a.num > b.num then .gt
    else compare a.den b.den
  | const _, _ => .lt
  | _, const _ => .gt
  | var a, var b => compare a b
  | var _, _ => .lt
  | _, var _ => .gt
  | sin a, sin b => cmpExpr a b
  | sin _, _ => .lt
  | _, sin _ => .gt
  | cos a, cos b => cmpExpr a b
  | cos _, _ => .lt
  | _, cos _ => .gt
  | tan a, tan b => cmpExpr a b
  | tan _, _ => .lt
  | _, tan _ => .gt
  | exp a, exp b => cmpExpr a b
  | exp _, _ => .lt
  | _, exp _ => .gt
  | ln a, ln b => cmpExpr a b
  | ln _, _ => .lt
  | _, ln _ => .gt
  | pow a1 b1, pow a2 b2 =>
    match cmpExpr a1 a2 with
    | .eq => cmpExpr b1 b2
    | o => o
  | pow _ _, _ => .lt
  | _, pow _ _ => .gt
  | mul a1 b1, mul a2 b2 =>
    match cmpExpr a1 a2 with
    | .eq => cmpExpr b1 b2
    | o => o
  | mul _ _, _ => .lt
  | _, mul _ _ => .gt
  | add a1 b1, add a2 b2 =>
    match cmpExpr a1 a2 with
    | .eq => cmpExpr b1 b2
    | o => o

partial def sortExprs (xs : List Expr) : List Expr :=
  xs.toArray.qsort (fun a b => cmpExpr a b == .lt) |>.toList

def foldAdd : List Expr → Expr
  | [] => zero
  | x :: xs => xs.foldl add x

def foldMul : List Expr → Expr
  | [] => one
  | x :: xs => xs.foldl mul x

/-- Split `c * rest` from a product (or treat whole as coefficient 1). -/
partial def splitCoeff : Expr → RatConst × Expr
  | mul (const c) e =>
    let (c', e') := splitCoeff e
    (c * c', e')
  | mul e (const c) =>
    let (c', e') := splitCoeff e
    (c * c', e')
  | const c => (c, one)
  | e => (RatConst.one, e)

/-- Base^exponent factors in a product list, with rational coefficient. -/
structure PowerFactor where
  base : Expr
  exp  : Expr
  deriving Repr

/-- Combine like summands: `2x + 3x → 5x`. -/
partial def combineSummands (terms : List Expr) : List Expr :=
  let tagged := terms.map splitCoeff
  -- group by structural equality of the non-constant part
  let rec insert (c : RatConst) (e : Expr) :
      List (RatConst × Expr) → List (RatConst × Expr)
    | [] => if c.isZero then [] else [(c, e)]
    | (c', e') :: rest =>
      if e == e' then
        let csum := c + c'
        if csum.isZero then rest
        else (csum, e') :: rest
      else
        (c', e') :: insert c e rest
  let grouped := tagged.foldl (fun acc (c, e) => insert c e acc) []
  grouped.map fun (c, e) =>
    if e == one then const c
    else if c.isOne then e
    else if c.isZero then zero
    else mul (const c) e

/-- Combine like factors: `x * x → x^2`, `x^a * x^b → x^(a+b)`. -/
partial def combineFactors (factors : List Expr) : List Expr :=
  -- extract (base, exp) pairs; constants collected separately
  let rec toPow : Expr → Option (Expr × Expr)
    | pow b e => some (b, e)
    | const _ => none
    | e => some (e, one)
  let mutConsts : List RatConst := factors.filterMap fun
    | const c => some c
    | _ => none
  let pows : List (Expr × Expr) := factors.filterMap toPow
  let rec insert (b e : Expr) : List (Expr × Expr) → List (Expr × Expr)
    | [] => [(b, e)]
    | (b', e') :: rest =>
      if b == b' then (b', add e e') :: rest
      else (b', e') :: insert b e rest
  let grouped := pows.foldl (fun acc (b, e) => insert b e acc) []
  let coeff := mutConsts.foldl (· * ·) RatConst.one
  let rebuilt := grouped.map fun (b, e) =>
    match e with
    | const r =>
      if r.isZero then one
      else if r.isOne then b
      else pow b e
    | _ => pow b e
  let rebuilt := rebuilt.filter (fun e => !(e == one))
  if coeff.isZero then [zero]
  else if coeff.isOne then rebuilt
  else const coeff :: rebuilt

/-- One bottom-up simplification pass. -/
partial def simplify1 : Expr → Expr
  | const r => const (RatConst.normalize r)
  | var v => var v
  | add a b =>
    let a := simplify1 a
    let b := simplify1 b
    match a, b with
    | const ra, const rb => const (ra + rb)
    | const r, e => if r.isZero then e else rebuildAdd (add (const r) e)
    | e, const r => if r.isZero then e else rebuildAdd (add e (const r))
    | _, _ => rebuildAdd (add a b)
  | mul a b =>
    let a := simplify1 a
    let b := simplify1 b
    match a, b with
    | const ra, const rb => const (ra * rb)
    | const r, _ =>
      if r.isZero then zero
      else if r.isOne then b
      else rebuildMul (mul a b)
    | _, const r =>
      if r.isZero then zero
      else if r.isOne then a
      else rebuildMul (mul a b)
    | _, _ => rebuildMul (mul a b)
  | pow a b =>
    let a := simplify1 a
    let b := simplify1 b
    match a, b with
    | _, const r =>
      if r.isZero then one
      else if r.isOne then a
      else match a with
        | const ra =>
          match RatConst.powInt ra r.num with
          -- only exact integer powers of rationals for now when den=1
          | some rc =>
            if r.den == 1 then const rc else pow a b
          | none => pow a b
        | pow base e => pow base (mul e b)  -- (x^m)^n = x^(m*n)
        | _ => pow a b
    | const r, _ =>
      if r.isOne then one
      else if r.isZero then zero  -- 0^e for e≠0; e=0 already handled
      else pow a b
    | _, _ => pow a b
  | sin e =>
    let e := simplify1 e
    match e with
    | const r => if r.isZero then zero else sin e
    | _ => sin e
  | cos e =>
    let e := simplify1 e
    match e with
    | const r => if r.isZero then one else cos e
    | _ => cos e
  | tan e =>
    let e := simplify1 e
    match e with
    | const r => if r.isZero then zero else tan e
    | _ => tan e
  | exp e =>
    let e := simplify1 e
    match e with
    | const r => if r.isZero then one else exp e
    | _ => exp e
  | ln e =>
    let e := simplify1 e
    match e with
    | const r => if r.isOne then zero else ln e
    | exp u => u
    | _ => ln e
where
  rebuildAdd (e : Expr) : Expr :=
    let terms := flattenAdd e
    let terms := combineSummands terms
    let terms := terms.filter (fun t => !(t == zero))
    let terms := sortExprs terms
    match terms with
    | [] => zero
    | _ => foldAdd terms
  rebuildMul (e : Expr) : Expr :=
    let factors := flattenMul e
    -- zero absorption
    if factors.any fun
      | const r => r.isZero
      | _ => false
    then zero
    else
      let factors := combineFactors factors
      let factors := factors.filter fun
        | const r => !r.isOne
        | e => !(e == one)
      let factors := sortExprs factors
      match factors with
      | [] => one
      | _ => foldMul factors

/-- Iterate simplification to a fixed point (bounded). -/
def simplify (e : Expr) (maxIters : Nat := 32) : Expr :=
  let rec go (n : Nat) (e : Expr) : Expr :=
    match n with
    | 0 => e
    | n'+1 =>
      let e' := simplify1 e
      if e' == e then e else go n' e'
  go maxIters e

/-- Expand products of sums: `(a+b)*(c+d) → ac+ad+bc+bd`. -/
partial def expand1 : Expr → Expr
  | add a b => add (expand1 a) (expand1 b)
  | mul a b =>
    let a := expand1 a
    let b := expand1 b
    match a, b with
    | add a1 a2, _ => add (expand1 (mul a1 b)) (expand1 (mul a2 b))
    | _, add b1 b2 => add (expand1 (mul a b1)) (expand1 (mul a b2))
    | _, _ => mul a b
  | pow a b =>
    let a := expand1 a
    match b with
    | const r =>
      if r.den == 1 && r.num > 1 && r.num ≤ 8 then
        -- expand small positive integer powers
        let rec powMul (k : Nat) (acc : Expr) : Expr :=
          match k with
          | 0 => acc
          | k'+1 => powMul k' (mul acc a)
        expand1 (powMul r.num.toNat one)
      else pow a b
    | _ => pow a b
  | sin e => sin (expand1 e)
  | cos e => cos (expand1 e)
  | tan e => tan (expand1 e)
  | exp e => exp (expand1 e)
  | ln e => ln (expand1 e)
  | e => e

def expand (e : Expr) : Expr := simplify (expand1 e)

end Taschenrechner.Expr
