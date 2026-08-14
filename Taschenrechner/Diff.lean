/-
  Symbolic differentiation.
-/
import Taschenrechner.Simplify

namespace Taschenrechner.Expr

/-- Symbolic derivative of `e` with respect to variable `v`. -/
partial def diff (e : Expr) (v : String := "x") : Expr :=
  simplify (diffRaw e v)
where
  diffRaw : Expr → String → Expr
    | const _, _ => zero
    | var name, v => if name == v then one else zero
    | add a b, v => add (diffRaw a v) (diffRaw b v)
    | mul a b, v =>
      -- product rule: (uv)' = u'v + uv'
      add (mul (diffRaw a v) b) (mul a (diffRaw b v))
    | pow a b, v =>
      -- general power: (u^v)' = u^v * (v' ln u + v u' / u)
      -- specialize when exponent is constant
      match b with
      | const r =>
        -- (u^n)' = n * u^(n-1) * u'
        let n := const r
        let nMinus1 := const (r - CplxConst.one)
        mul (mul n (pow a nMinus1)) (diffRaw a v)
      | _ =>
        if !dependsOn b v then
          -- (u^c)' = c * u^(c-1) * u'  for c independent of v
          mul (mul b (pow a (sub b one))) (diffRaw a v)
        else if !dependsOn a v then
          -- (c^v)' = c^v * ln(c) * v'
          mul (mul (pow a b) (ln a)) (diffRaw b v)
        else
          -- full formula
          let logDiff := add
            (mul (diffRaw b v) (ln a))
            (mul b (div (diffRaw a v) a))
          mul (pow a b) logDiff
    | sin a, v => mul (cos a) (diffRaw a v)
    | cos a, v => mul (neg (sin a)) (diffRaw a v)
    | tan a, v =>
      -- (tan u)' = (1 + tan^2 u) * u'
      mul (add one (pow (tan a) (ofInt 2))) (diffRaw a v)
    | sinh a, v => mul (cosh a) (diffRaw a v)
    | cosh a, v => mul (sinh a) (diffRaw a v)
    | tanh a, v =>
      -- (tanh u)' = (1 - tanh² u) * u'
      mul (sub one (pow (tanh a) (ofInt 2))) (diffRaw a v)
    | exp a, v => mul (exp a) (diffRaw a v)
    | ln a, v => div (diffRaw a v) a
    | atan a, v =>
      div (diffRaw a v) (add one (pow a (ofInt 2)))
    | asin a, v =>
      -- (asin u)' = u' / √(1 − u²)
      div (diffRaw a v) (pow (sub one (pow a (ofInt 2))) (ofRat ⟨1, 2⟩))
    | acos a, v =>
      -- (acos u)' = −u' / √(1 − u²)
      neg (div (diffRaw a v) (pow (sub one (pow a (ofInt 2))) (ofRat ⟨1, 2⟩)))
    | sec a, v =>
      mul (mul (sec a) (tan a)) (diffRaw a v)
    | csc a, v =>
      neg (mul (mul (csc a) (cot a)) (diffRaw a v))
    | cot a, v =>
      neg (mul (pow (csc a) (ofInt 2)) (diffRaw a v))
    | factorial _a, _v => zero  -- discrete; no digamma
    | gamma _a, _v => zero      -- Γ' needs digamma
    | floor _a, _v => zero      -- 0 a.e.
    | Expr.ite c t e, v =>
      Expr.ite c (diffRaw t v) (diffRaw e v)
    | abs a, v =>
      -- d/dx |u| = u' · u / |u|  (real; undefined at 0)
      mul (div a (abs a)) (diffRaw a v)
    | re a, v => re (diffRaw a v)
    | im a, v => im (diffRaw a v)
    | conj a, v => conj (diffRaw a v)
    | eq a b, v => eq (diffRaw a v) (diffRaw b v)
    | lt a b, v => lt (diffRaw a v) (diffRaw b v)
    | le a b, v => le (diffRaw a v) (diffRaw b v)
    | mat rows, v =>
      mat (rows.map (fun row => row.map (fun e => diffRaw e v)))

/-- n-th derivative. -/
def diffN (e : Expr) (n : Nat) (v : String := "x") : Expr :=
  match n with
  | 0 => simplify e
  | n'+1 => diffN (diff e v) n' v

/-- Partial derivative helper. -/
def partialDiff (e : Expr) (v : String) : Expr := diff e v

end Taschenrechner.Expr
