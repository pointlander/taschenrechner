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
import Taschenrechner.Env
import Taschenrechner.Normal
import Taschenrechner.Eval

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

-- Matrices
#guard
  match parse "[1, 2; 3, 4]" with
  | .ok (.mat rows) =>
      Mat.nrows rows == 2 && Mat.ncols rows == 2
        && rows[0]![0]! == (1 : Expr) && rows[1]![1]! == (4 : Expr)
  | _ => false
#guard
  match parse "det([1, 2; 3, 4])" with
  | .ok e => simplify e == ofInt (-2)
  | _ => false
#guard
  match parse "eye(2)" with
  | .ok (.mat rows) =>
      rows[0]![0]! == (1 : Expr) && rows[0]![1]! == (0 : Expr)
        && rows[1]![0]! == (0 : Expr) && rows[1]![1]! == (1 : Expr)
  | _ => false
#guard
  match parse "[1, 2; 3, 4] * [0, 1; 1, 0]" with
  | .ok e =>
      match simplify e with
      | .mat rows =>
          rows[0]![0]! == (2 : Expr) && rows[0]![1]! == (1 : Expr)
            && rows[1]![0]! == (4 : Expr) && rows[1]![1]! == (3 : Expr)
      | _ => false
  | _ => false
#guard
  match parse "trace([1, 2; 3, 4])" with
  | .ok e => simplify e == (5 : Expr)
  | _ => false
#guard
  match parse "transpose([1, 2; 3, 4])" with
  | .ok (.mat rows) =>
      rows[0]![0]! == (1 : Expr) && rows[0]![1]! == (3 : Expr)
        && rows[1]![0]! == (2 : Expr) && rows[1]![1]! == (4 : Expr)
  | _ => false

-- Environment bindings
#guard
  match envAssign Env.empty "A" (ofInt 3) with
  | .ok (env, _) =>
      match env.get? "A", substEnv env (var "A" + var "A") with
      | some _, e => simplify e == ofInt 6
      | _, _ => false
  | .error _ => false
#guard
  match parseCommand "A := 1+2" with
  | .ok (.assign "A" e) => simplify e == ofInt 3
  | _ => false
#guard
  match parse "[1, 2; 3, 4]" with
  | .ok m =>
    match envAssign Env.empty "M" m with
    | .ok (env, _) =>
      match parse "det(M)" env with
      | .ok e => simplify e == ofInt (-2)
      | _ => false
    | _ => false
  | _ => false
#guard
  match parseCommand "vars" with
  | .ok .vars => true
  | _ => false
#guard
  match parseCommand "clear" with
  | .ok .clearAll => true
  | _ => false
#guard
  match parseCommand "clear A" with
  | .ok (.clearOne "A") => true
  | _ => false
#guard
  match envAssign Env.empty "i" (ofInt 1) with
  | .error _ => true
  | .ok _ => false

-- Multi-statement split (matrix `;` stays intact)
#guard
  let parts := splitStatements "A := [1, 2; 3, 4]; det(A)"
  parts.length == 2
    && parts[0]! == "A := [1, 2; 3, 4]"
    && parts[1]! == "det(A)"
#guard
  splitStatements "1+2" == ["1+2"]
#guard
  match parseCommand "save foo.tr" with
  | .ok (.save "foo.tr") => true
  | _ => false
#guard
  match parseCommand "load foo.tr" with
  | .ok (.load "foo.tr") => true
  | _ => false
#guard
  let env := Env.setAns Env.empty (ofInt 7)
  match env.get? "ans" with
  | some e => simplify e == ofInt 7
  | none => false
#guard
  let body := Env.toSession (Env.set Env.empty "A" (ofInt 3))
  body.contains "A := 3"

-- Normal forms
#guard
  -- x/x → 1
  simplify (cancel (x / x)) == (1 : Expr)
#guard
  -- 2x/x → 2
  simplify (cancel (((2 : Expr) * x) / x)) == (2 : Expr)
#guard
  -- poly GCD cancel: (x²−1)/(x−1) → x+1
  equivNF (cancel ((x ^ (2 : Expr) - 1) / (x - 1))) (x + 1)
#guard
  -- 1/x + 1/(x+1) together
  let e := together ((1 : Expr) / x + (1 : Expr) / (x + 1))
  match RatFn.ofExpr? e "x" with
  | some r =>
      -- ( (x+1) + x ) / (x(x+1)) = (2x+1)/(x^2+x)
      !r.den.isOne && !(r.num.isZero)
  | none => false
#guard isZeroExpr (x - x)
#guard isZeroExpr (((1 : Expr) / x) * x - 1)
#guard equivNF ((1 : Expr) / x + (1 : Expr) / x) ((2 : Expr) / x)
#guard
  match parse "nf(1/x + 2/x)" with
  | .ok e => equivNF e ((3 : Expr) / x)
  | _ => false
#guard
  match parse "together(1/x + 1/(x+1))" with
  | .ok e =>
      match RatFn.ofExpr? e "x" with
      | some _ => true
      | none => false
  | _ => false
#guard
  match parse "cancel((x^2-1)/(x-1))" with
  | .ok e => equivNF e (x + 1)
  | _ => false

-- Substitution & evaluation
#guard simplify (subst (x ^ (2 : Expr) + 1) "x" (ofInt 3)) == ofInt 10
#guard
  match evalAt? (x ^ (2 : Expr) + (2 : Expr) * x + 1) "x" (CplxConst.ofInt 2) with
  | some c => c == CplxConst.ofInt 9
  | none => false
#guard
  match eval? (simplify ((2 : Expr) + (3 : Expr) * I)) with
  | some c => c.re == RatConst.ofInt 2 && c.im == RatConst.ofInt 3
  | none => false
#guard
  match parse "subst(x^2+1, x, 3)" with
  | .ok e => e == ofInt 10
  | _ => false
#guard
  match parse "eval(2+3*i)" with
  | .ok e => e == ofCplx ⟨RatConst.ofInt 2, RatConst.ofInt 3⟩
  | _ => false
#guard
  match parse "eval(x^2+1, x, 4)" with
  | .ok e => e == ofInt 17
  | _ => false
#guard
  -- fraction pretty-print: 1/x and 3/x
  Expr.toString ((1 : Expr) / x) == "1/x"
#guard Expr.toString (((3 : Expr) / x)) == "3/x"
#guard
  -- (x^2-1)/(x-1) after cancel prints without ·x^-1
  let s := Expr.toString (cancel ((x ^ (2 : Expr) - 1) / (x - 1)))
  s == "1 + x" || s == "x + 1"

end Taschenrechner.Tests
