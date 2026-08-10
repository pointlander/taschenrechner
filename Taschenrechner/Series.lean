/-
  Taylor / Maclaurin series expansion.

  `taylor f v a n` = ∑_{k=0}^{n} f^{(k)}(a) / k! · (v − a)^k
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Eval

namespace Taschenrechner

open Expr

/-- `n!` as a natural number. -/
def natFactorial : Nat → Nat
  | 0 => 1
  | n'+1 => (n'+1) * natFactorial n'

/-- `n!` as an expression constant. -/
def factorialExpr (n : Nat) : Expr :=
  Expr.ofNat (natFactorial n)

/--
  Taylor polynomial of `f` in free variable `v`, expanded about `a`,
  of degree at most `n`.

  Coefficients are obtained by differentiating and substituting `v ↦ a`
  (exact eval in ℚ(i) when possible).
-/
def taylor (f : Expr) (v : String) (a : Expr) (n : Nat) : Expr :=
  Id.run do
    let mut acc : Expr := zero
    let mut dk : Expr := simplify f
    for k in [0:n+1] do
      let ck := evalAtOrSimplify dk v a
      let term : Expr :=
        if k == 0 then ck
        else
          let powTerm :=
            if a == zero then
              -- Maclaurin: (v)^k
              if k == 1 then var v else pow (var v) (ofNat k)
            else
              let u := sub (var v) a
              if k == 1 then u else pow u (ofNat k)
          mul (div ck (factorialExpr k)) powTerm
      acc := add acc term
      dk := diff dk v
    pure (simplify acc)

/-- Maclaurin series: Taylor about 0. -/
def maclaurin (f : Expr) (v : String) (n : Nat) : Expr :=
  taylor f v zero n

/-- Convenience: Taylor about 0 in `"x"`. -/
def series (f : Expr) (n : Nat) (v : String := "x") : Expr :=
  maclaurin f v n

end Taschenrechner
