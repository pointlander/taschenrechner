/-
  Guard tests for the CAS core.
  These are type-checked / evaluated at compile time via `#guard`.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Diff
import Taschenrechner.Integrate
import Taschenrechner.Parse
import Taschenrechner.Risch

namespace Taschenrechner.Tests

open Expr
open Parse
open Taschenrechner

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
  | .success r _ => r == ofRat ⟨1, 3⟩
  | _ => false

-- Complex arithmetic
#guard simplify (I * I) == negOne
#guard simplify (I ^ (2 : Expr)) == negOne
#guard simplify ((2 : Expr) + (3 : Expr) * I) == const ⟨⟨2, 1⟩, ⟨3, 1⟩⟩
#guard simplify (re ((2 : Expr) + (3 : Expr) * I)) == (2 : Expr)
#guard simplify (im ((2 : Expr) + (3 : Expr) * I)) == (3 : Expr)
#guard simplify (conj ((2 : Expr) + (3 : Expr) * I)) == const ⟨⟨2, 1⟩, ⟨-3, 1⟩⟩
#guard
  match CplxConst.div ⟨⟨1, 1⟩, ⟨0, 1⟩⟩ ⟨⟨0, 1⟩, ⟨1, 1⟩⟩ with
  | some z => z == ⟨⟨0, 1⟩, ⟨-1, 1⟩⟩  -- 1/i = -i
  | none => false

-- Structured integrate results
#guard
  match integrate (exp x) "x" with
  | .success _ .risch => true
  | _ => false
#guard
  match integrate (sin x) "x" with
  | .success _ .risch => true
  | _ => false

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
#guard parseEq "i" I
#guard parseEq "I" I
#guard parseEq "2+3*i" (const ⟨⟨2, 1⟩, ⟨3, 1⟩⟩)
#guard parseEq "i^2" negOne
#guard parseEq "re(2+3*i)" (2 : Expr)
#guard parseEq "im(2+3*i)" (3 : Expr)

-- Command parser
#guard
  match parseCommand "diff sin(x)" with
  | .ok (.diff e "x") => e == sin x
  | _ => false
#guard
  match parseCommand "int x^2 x" with
  | .ok (.integrate e "x") => e == x ^ (2 : Expr)
  | _ => false

-- Risch: rational
#guard
  match risch (Expr.div (1 : Expr) x) "x" with
  | .elementary F => simplify (diff F "x") == simplify (Expr.div (1 : Expr) x)
  | _ => false
#guard
  match risch (Expr.div (1 : Expr) (x ^ (2 : Expr) + 1)) "x" with
  | .elementary F => F == atan x || simplify (diff F "x") == simplify (Expr.div (1 : Expr) (x ^ (2 : Expr) + 1))
  | _ => false

-- Risch: exp DE
#guard
  match risch (exp x) "x" with
  | .elementary F => simplify (diff F "x") == exp x
  | _ => false
#guard
  match risch (exp ((2 : Expr) * x)) "x" with
  | .elementary F => simplify (diff F "x") == exp ((2 : Expr) * x)
  | _ => false
#guard
  match risch (x * exp (x ^ (2 : Expr))) "x" with
  | .elementary F =>
      let d := simplify (diff F "x")
      d == simplify (x * exp (x ^ (2 : Expr)))
  | _ => false

-- Risch: non-existence certificate for ∫ e^{x²} dx
#guard rischNotElementary (exp (x ^ (2 : Expr))) "x"
#guard
  match integrate (exp (x ^ (2 : Expr))) "x" with
  | .notElementary _ => true
  | _ => false

-- Automatic verification helpers
#guard verifyDerivative (atan x) (Expr.div (1 : Expr) (x ^ (2 : Expr) + 1)) "x"
#guard verifyDerivative (exp x) (exp x) "x"

-- Complex differentiation / integration
#guard simplify (diff (I * x) "x") == I
#guard simplify (diff (I * sin x) "x") == I * cos x
#guard simplify (diff (exp (I * x)) "x") == I * exp (I * x)
#guard
  match integrate (I * sin x) "x" with
  | .success F _ => verifyDerivative F (I * sin x) "x"
  | _ => false
#guard
  match integrate (exp (I * x)) "x" with
  | .success F _ => verifyDerivative F (exp (I * x)) "x"
  | _ => false
#guard
  match integrate (((2 : Expr) + (3 : Expr) * I) * x) "x" with
  | .success F _ => verifyDerivative F (((2 : Expr) + (3 : Expr) * I) * x) "x"
  | _ => false
#guard simplify (re (I * x)) == (0 : Expr)
#guard simplify (im (I * x)) == x

end Taschenrechner.Tests
