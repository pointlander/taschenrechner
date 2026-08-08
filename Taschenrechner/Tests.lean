/-
  Guard tests for the CAS core.
  These are type-checked / evaluated at compile time via `#guard`.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Integrate
import Taschenrechner.Parse

namespace Taschenrechner.Tests

open Expr
open Parse

/-- Parse must succeed and equal `expected` (after simplify). -/
def parseEq (s : String) (expected : Expr) : Bool :=
  match parse s with
  | .ok e => e == simplify expected
  | .error _ => false

-- Rational arithmetic
#guard (RatConst.ofInt 2 + RatConst.ofInt 3) == RatConst.ofInt 5
#guard (RatConst.ofInt 2 * RatConst.ofInt 3) == RatConst.ofInt 6
#guard (RatConst.normalize ⟨2, 4⟩) == (⟨1, 2⟩ : RatConst)

-- Simplification
#guard simplify ((0 : Expr) + x) == x
#guard simplify (x + (0 : Expr)) == x
#guard simplify ((1 : Expr) * x) == x
#guard simplify (x * (0 : Expr)) == (0 : Expr)
#guard simplify ((2 : Expr) + (3 : Expr)) == (5 : Expr)
#guard simplify (x + x) == (2 : Expr) * x
#guard simplify (x * x) == x ^ (2 : Expr)

-- Differentiation
#guard diff (x ^ (2 : Expr)) "x" == (2 : Expr) * x
#guard diff (sin x) "x" == cos x
#guard diff (exp x) "x" == exp x
#guard simplify (diff (ln x) "x" * x) == (1 : Expr)
#guard diff ((3 : Expr) * x + (1 : Expr)) "x" == (3 : Expr)
#guard simplify (diff (cos x) "x" + sin x) == (0 : Expr)

-- Integration succeeds
#guard (integrate (x ^ (2 : Expr)) "x").isSuccess
#guard (integrate (sin x) "x").isSuccess
#guard (integrate (exp x) "x").isSuccess
#guard (integrate ((3 : Expr) * x + 1) "x").isSuccess

-- Antiderivative checks (F' = f)
#guard checkAntiderivative (x ^ (2 : Expr)) "x"
#guard checkAntiderivative (sin x) "x"
#guard checkAntiderivative (cos x) "x"
#guard checkAntiderivative (exp x) "x"
#guard checkAntiderivative ((5 : Expr) * x + (2 : Expr)) "x"
#guard checkAntiderivative (x ^ ((-1 : Expr))) "x"
#guard checkAntiderivative (cos ((2 : Expr) * x)) "x"
#guard checkAntiderivative (exp ((3 : Expr) * x)) "x"

-- Definite integral ∫₀¹ x² dx = 1/3
#guard
  match integrateDefinite (x ^ (2 : Expr)) "x" (0 : Expr) (1 : Expr) with
  | .success r => r == const ⟨1, 3⟩
  | .failure _ => false

-- Parser
#guard parseEq "0" (0 : Expr)
#guard parseEq "42" (42 : Expr)
#guard parseEq "x" x
#guard parseEq "x + 1" (x + 1)
#guard parseEq "x^2" (x ^ (2 : Expr))
#guard parseEq "2*x" ((2 : Expr) * x)
#guard parseEq "2x" ((2 : Expr) * x)
#guard parseEq "x^2 + 3*x + 1" (x ^ (2 : Expr) + (3 : Expr) * x + 1)
#guard parseEq "sin(x)" (sin x)
#guard parseEq "cos(2*x)" (cos ((2 : Expr) * x))
#guard parseEq "exp(x)" (exp x)
#guard parseEq "ln(x)" (ln x)
#guard parseEq "1/x" ((1 : Expr) / x)
#guard parseEq "(x+1)*(x-1)" ((x + 1) * (x - 1))
#guard parseEq "2x(x+1)" ((2 : Expr) * x * (x + 1))
#guard parseEq "-x^2" (neg (x ^ (2 : Expr)))
#guard parseEq "a^b^c" (Expr.pow (var "a") (Expr.pow (var "b") (var "c")))
#guard parseEq "diff(x^2)" ((2 : Expr) * x)
#guard parseEq "diff(sin(x), x)" (cos x)
#guard parseEq "diff(sin(x^2), x)" ((2 : Expr) * x * cos (x ^ (2 : Expr)))
#guard parseEq "int(x^2)" ((1 : Expr) / (3 : Expr) * (x ^ (3 : Expr)))
#guard parseEq "simplify(x+x)" ((2 : Expr) * x)

-- Command parser
#guard
  match parseCommand "diff sin(x)" with
  | .ok (.diff e "x") => e == sin x
  | _ => false
#guard
  match parseCommand "int x^2 x" with
  | .ok (.integrate e "x") => e == x ^ (2 : Expr)
  | _ => false

end Taschenrechner.Tests
