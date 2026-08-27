/-
  Multivariate polynomials over ℚ and lex Gröbner bases (Buchberger).

  Variable order: `vars[0] > vars[1] > … > vars[last]` (lex, first index largest).
  Caps on pairs / generators keep compile-time `#guard`s bounded.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Poly
import Taschenrechner.RatInt

namespace Taschenrechner

open Expr

def groebnerMaxPairs : Nat := 80
def groebnerMaxGens : Nat := 24
def groebnerReduceFuel : Nat := 128

/-- Exponent vector, length = number of variables. -/
structure Mono where
  exps : Array Nat
  deriving Repr, Inhabited

namespace Mono

def nvars (m : Mono) : Nat := m.exps.size

def zero (n : Nat) : Mono := ⟨Array.replicate n 0⟩

def isZero (m : Mono) : Bool := m.exps.all (· == 0)

def beq (a b : Mono) : Bool :=
  a.exps.size == b.exps.size &&
    Id.run do
      for i in [:a.exps.size] do
        if a.exps[i]! != b.exps[i]! then return false
      pure true

instance : BEq Mono where beq := beq

/-- Lex: first differing index, larger exponent wins (`vars[0]` largest). -/
def lexCmp (a b : Mono) : Ordering :=
  let n := min a.exps.size b.exps.size
  Id.run do
    for i in [:n] do
      if a.exps[i]! > b.exps[i]! then return .gt
      if a.exps[i]! < b.exps[i]! then return .lt
    if a.exps.size > b.exps.size then pure .gt
    else if a.exps.size < b.exps.size then pure .lt
    else pure .eq

def lexLt (a b : Mono) : Bool := lexCmp a b == .lt

def zipNat (op : Nat → Nat → Nat) (a b : Array Nat) : Array Nat :=
  Id.run do
    let n := min a.size b.size
    let mut e : Array Nat := Array.replicate n 0
    for i in [:n] do
      e := e.set! i (op a[i]! b[i]!)
    pure e

def mul (a b : Mono) : Mono :=
  ⟨zipNat (· + ·) a.exps b.exps⟩

def divides (a b : Mono) : Bool :=
  a.exps.size == b.exps.size &&
    Id.run do
      for i in [:a.exps.size] do
        if a.exps[i]! > b.exps[i]! then return false
      pure true

def div? (num den : Mono) : Option Mono :=
  if divides den num then
    some ⟨zipNat (· - ·) num.exps den.exps⟩
  else none

def lcm (a b : Mono) : Mono :=
  ⟨zipNat max a.exps b.exps⟩

def coprime (a b : Mono) : Bool :=
  a.exps.size == b.exps.size &&
    Id.run do
      for i in [:a.exps.size] do
        if a.exps[i]! > 0 && b.exps[i]! > 0 then return false
      pure true

def ofVar (i n : Nat) : Mono :=
  ⟨Array.replicate n 0 |>.set! i 1⟩

def pow (m : Mono) (k : Nat) : Mono :=
  ⟨m.exps.map (· * k)⟩

def totalDeg (m : Mono) : Nat :=
  m.exps.foldl (· + ·) 0

end Mono

/-- Sparse multivariate polynomial; terms sorted descending lex. -/
structure MPoly where
  vars  : List String
  terms : List (Mono × RatConst)
  deriving Repr, Inhabited

namespace MPoly

def nvars (p : MPoly) : Nat := p.vars.length

def zero (vars : List String) : MPoly := ⟨vars, []⟩
def isZero (p : MPoly) : Bool := p.terms.isEmpty

def ofConst (vars : List String) (c : RatConst) : MPoly :=
  if c.isZero then zero vars
  else ⟨vars, [(Mono.zero vars.length, RatConst.normalize c)]⟩

def one (vars : List String) : MPoly := ofConst vars RatConst.one

def isOne (p : MPoly) : Bool :=
  match p.terms with
  | [(m, c)] => m.isZero && c.isOne
  | _ => false

/-- Insert `c · m` into a descending-lex term list. -/
def insertTerm (m : Mono) (c : RatConst) : List (Mono × RatConst) → List (Mono × RatConst)
  | [] => if c.isZero then [] else [(m, RatConst.normalize c)]
  | (m', c') :: rest =>
    match Mono.lexCmp m m' with
    | .eq =>
      let s := RatConst.normalize (c + c')
      if s.isZero then rest else (m', s) :: rest
    | .gt =>
      if c.isZero then (m', c') :: rest else (m, RatConst.normalize c) :: (m', c') :: rest
    | .lt => (m', c') :: insertTerm m c rest

def strip (p : MPoly) : MPoly :=
  ⟨p.vars, p.terms.filter fun (_, c) => !c.isZero⟩

def add (a b : MPoly) : MPoly :=
  let vars := if a.vars.isEmpty then b.vars else a.vars
  ⟨vars, b.terms.foldl (fun acc (m, c) => insertTerm m c acc) a.terms⟩

def neg (p : MPoly) : MPoly :=
  ⟨p.vars, p.terms.map fun (m, c) => (m, RatConst.neg c)⟩

def sub (a b : MPoly) : MPoly := add a (neg b)

def scale (c : RatConst) (p : MPoly) : MPoly :=
  if c.isZero then zero p.vars
  else ⟨p.vars, p.terms.filterMap fun (m, k) =>
    let s := RatConst.normalize (c * k)
    if s.isZero then none else some (m, s)⟩

def mulTerm (m : Mono) (c : RatConst) (p : MPoly) : MPoly :=
  if c.isZero then zero p.vars
  else
    ⟨p.vars, p.terms.foldl (fun acc (m', k) =>
      insertTerm (Mono.mul m m') (c * k) acc) []⟩

def mul (a b : MPoly) : MPoly :=
  a.terms.foldl (fun acc (m, c) => add acc (mulTerm m c b)) (zero a.vars)

def lm? (p : MPoly) : Option Mono :=
  match p.terms with
  | (m, _) :: _ => some m
  | [] => none

def lc? (p : MPoly) : Option RatConst :=
  match p.terms with
  | (_, c) :: _ => some c
  | [] => none

def monic (p : MPoly) : MPoly :=
  match lc? p with
  | none => p
  | some c =>
    match RatConst.inv c with
    | some i => scale i p
    | none => p

/-- Variables that actually appear (nonzero exponent). -/
def varsUsed (p : MPoly) : List String :=
  let n := p.vars.length
  Id.run do
    let mut out : List String := []
    for i in [:n] do
      let used := p.terms.any fun (m, _) => i < m.exps.size && m.exps[i]! > 0
      if used then
        match p.vars[i]? with
        | some v => out := out ++ [v]
        | none => pure ()
    pure out

def onlyVars (p : MPoly) (allowed : List String) : Bool :=
  varsUsed p |>.all (allowed.contains)

/-- Univariate `Poly` in `v` when no other variable appears. -/
def toUnivariate? (p : MPoly) (v : String) : Option Poly :=
  if !(onlyVars p [v]) then none
  else
    match p.vars.findIdx? (· == v) with
    | none =>
      -- constant
      match p.terms with
      | [] => some Poly.zero
      | [(_, c)] => some (Poly.ofConst c)
      | _ => none
    | some i =>
      let deg :=
        p.terms.foldl (fun d (m, _) =>
          let e := m.exps[i]?.getD 0
          max d e) 0
      Id.run do
        let mut cs : Array RatConst := Array.replicate (deg + 1) RatConst.zero
        for (m, c) in p.terms do
          let e := m.exps[i]?.getD 0
          if e ≤ deg then
            cs := cs.set! e (cs[e]! + c)
        pure (some (Poly.strip ⟨cs⟩))

/-- Reconstruct an expression. -/
def toExpr (p : MPoly) : Expr :=
  match p.terms with
  | [] => Expr.zero
  | ts =>
    let termE (m : Mono) (c : RatConst) : Expr :=
      let body :=
        Id.run do
          let mut acc : Expr := Expr.one
          for i in [:p.vars.length] do
            let e := m.exps[i]?.getD 0
            if e > 0 then
              let v := Expr.var p.vars[i]!
              let pe := if e == 1 then v else Expr.pow v (Expr.ofNat e)
              acc := if acc == Expr.one then pe else Expr.mul acc pe
          pure acc
      if c.isOne then body
      else if body == Expr.one then Expr.ofRat c
      else Expr.mul (Expr.ofRat c) body
    match ts with
    | (m, c) :: rest =>
      rest.foldl (fun acc (m, c) => Expr.add acc (termE m c)) (termE m c)
    | [] => Expr.zero

/-- Parse a polynomial in the given variables (others → fail). -/
partial def ofExpr? (e : Expr) (vars : List String) : Option MPoly :=
  go (simplify e)
where
  go : Expr → Option MPoly
  | .const r =>
    match CplxConst.toRat? r with
    | some q => some (ofConst vars q)
    | none => none
  | .var name =>
    match vars.findIdx? (· == name) with
    | some i => some ⟨vars, [(Mono.ofVar i vars.length, RatConst.one)]⟩
    | none => none
  | .add a b =>
    match go a, go b with
    | some pa, some pb => some (add pa pb)
    | _, _ => none
  | .mul a b =>
    match go a, go b with
    | some pa, some pb => some (mul pa pb)
    | _, _ => none
  | .pow base (.const r) =>
    match CplxConst.toRat? r with
    | none => none
    | some q =>
      if q.den != 1 || q.num < 0 then none
      else
        match go base with
        | none => none
        | some pb =>
          some (powNat pb q.num.toNat)
  | .pow _ _ => none
  | _ => none

  powNat (p : MPoly) : Nat → MPoly
    | 0 => one vars
    | n'+1 => mul (powNat p n') p

end MPoly

/-! ### Reduction and Buchberger -/

/-- One reduction step: cancel a term of `f` using `g`. -/
def reduceStep (f g : MPoly) : Option MPoly :=
  if g.isZero then none
  else
    match MPoly.lm? g, MPoly.lc? g with
    | none, _ | _, none => none
    | some mg, some cg =>
      Id.run do
        for (mf, cf) in f.terms do
          if Mono.divides mg mf then
            match Mono.div? mf mg, RatConst.div cf cg with
            | some t, some c =>
              return some (MPoly.sub f (MPoly.mulTerm t c g))
            | _, _ => pure ()
        pure none

partial def reduce (f : MPoly) (G : List MPoly) (fuel : Nat := groebnerReduceFuel) : MPoly :=
  match fuel with
  | 0 => f
  | fuel'+1 =>
    if f.isZero then f
    else
      match G.findSome? (fun g => reduceStep f g) with
      | some f' => reduce f' G fuel'
      | none => f

/-- S-polynomial. -/
def sPoly (f g : MPoly) : Option MPoly :=
  match MPoly.lm? f, MPoly.lm? g, MPoly.lc? f, MPoly.lc? g with
  | some mf, some mg, some cf, some cg =>
    let γ := Mono.lcm mf mg
    match Mono.div? γ mf, Mono.div? γ mg, RatConst.inv cf, RatConst.inv cg with
    | some tf, some tg, some iff, some ig =>
      some (MPoly.sub (MPoly.mulTerm tf iff f) (MPoly.mulTerm tg ig g))
    | _, _, _, _ => none
  | _, _, _, _ => none

/-- Drop generators whose leading monomial is a multiple of another. -/
def minimize (G : List MPoly) : List MPoly :=
  let G := (G.filter (fun p => !p.isZero) |>.map MPoly.monic).toArray
  Id.run do
    let mut keep := Array.replicate G.size true
    for i in [:G.size] do
      if keep[i]! then
        match MPoly.lm? G[i]! with
        | none => keep := keep.set! i false
        | some mi =>
          for j in [:G.size] do
            if i != j && keep[j]! then
              match MPoly.lm? G[j]! with
              | some mj =>
                if Mono.divides mj mi then
                  if Mono.beq mi mj then
                    if i > j then keep := keep.set! i false
                  else
                    keep := keep.set! i false
              | none => pure ()
    let mut out : List MPoly := []
    for i in [:G.size] do
      if keep[i]! then out := out ++ [G[i]!]
    pure out

/-- Reduced Gröbner basis: minimal, then tails reduced modulo the others. -/
def reduceBasis (G : List MPoly) : List MPoly :=
  let G := minimize G
  let arr := G.toArray
  let reduced :=
    Id.run do
      let mut out : List MPoly := []
      for i in [:arr.size] do
        let others :=
          (List.range arr.size).filterMap fun j =>
            if j == i then none else some arr[j]!
        let r := MPoly.monic (reduce arr[i]! others)
        if !r.isZero then
          out := out ++ [r]
      pure out
  (minimize reduced).mergeSort fun a b =>
    match MPoly.lm? a, MPoly.lm? b with
    | some ma, some mb => !Mono.lexLt ma mb
    | some _, none => true
    | none, some _ => false
    | none, none => true

/-- Buchberger with pair/generator caps. Leading monomials made monic. -/
def buchberger (F : List MPoly) : List MPoly :=
  let F := F.filter (fun p => !p.isZero) |>.map MPoly.monic
  if F.isEmpty then []
  else if F.any MPoly.isOne then
    let vars := F.head!.vars
    [MPoly.one vars]
  else
    Id.run do
      let mut G : Array MPoly := F.toArray
      let mut pairs : List (Nat × Nat) := []
      for i in [:G.size] do
        for j in [i + 1:G.size] do
          pairs := pairs ++ [(i, j)]
      let mut steps : Nat := 0
      while !pairs.isEmpty && steps < groebnerMaxPairs && G.size ≤ groebnerMaxGens do
        steps := steps + 1
        match pairs with
        | [] => pure ()
        | (i, j) :: rest =>
          pairs := rest
          if i < G.size && j < G.size then
            let f := G[i]!
            let g := G[j]!
            let skip :=
              match MPoly.lm? f, MPoly.lm? g with
              | some mf, some mg => Mono.coprime mf mg
              | _, _ => true
            if !skip then
              match sPoly f g with
              | none => pure ()
              | some s =>
                let r := MPoly.monic (reduce s G.toList)
                if r.isOne then
                  G := #[r]
                  pairs := []
                else if !r.isZero then
                  let k := G.size
                  G := G.push r
                  for t in [:k] do
                    pairs := pairs ++ [(t, k)]
      pure (reduceBasis (G.toList))

/-- Gröbner basis of residuals in the given variable order. -/
def groebnerBasis (es : List Expr) (vars : List String) : Option (List MPoly) :=
  let ps := es.filterMap (fun e => MPoly.ofExpr? e vars)
  if ps.length != es.length then none
  else some (buchberger ps)

/-- Gröbner generators as expressions (column matrix for the REPL). -/
def groebnerExprs (es : List Expr) (vars : List String) : Option Expr :=
  match groebnerBasis es vars with
  | none => none
  | some G =>
    if G.isEmpty then some Expr.zero
    else
      let rows := G.toArray.map fun p => #[simplify (MPoly.toExpr p)]
      some (Expr.mat rows)

end Taschenrechner
