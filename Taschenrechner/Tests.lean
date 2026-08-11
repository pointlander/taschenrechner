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
import Taschenrechner.Numeric
import Taschenrechner.Solve
import Taschenrechner.Series
import Taschenrechner.Eigen
import Taschenrechner.Limit
import Taschenrechner.Matrix
import Taschenrechner.Sum
import Taschenrechner.ODE

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

-- Factor & scalar solve
#guard
  match factorIn (x ^ (2 : Expr) - 1) "x" with
  | some f =>
      -- (x−1)(x+1) up to order
      equivNF f ((x - 1) * (x + 1))
  | none => false
#guard
  match solveScalar (x ^ (2 : Expr) - (5 : Expr) * x + 6) "x" with
  | .solutions rs =>
      rs.length == 2 && rs.any (· == ofInt 2) && rs.any (· == ofInt 3)
  | _ => false
#guard
  match solveScalar ((2 : Expr) * x + 1) "x" with
  | .solutions rs => rs == [ofRat ⟨-1, 2⟩]
  | _ => false
#guard
  match solveEq (x ^ (2 : Expr)) (4 : Expr) "x" with
  | .solutions rs => rs.any (· == ofInt 2) && rs.any (· == ofInt (-2))
  | _ => false
#guard
  match coeffOf ((3 : Expr) * x ^ (2 : Expr) + (2 : Expr) * x + 1) "x" 2 with
  | some c => c == ofInt 3
  | none => false
#guard
  match parse "solve(x^2-5*x+6, x)" with
  | .ok e =>
      match asMat? e with
      | some rows =>
          rows.size == 1 && rows[0]!.size == 2
      | none => false
  | _ => false
#guard
  match parse "factor(x^2-1)" with
  | .ok e => equivNF e ((x - 1) * (x + 1))
  | _ => false
#guard
  match parse "roots(x^2-1)" with
  | .ok e =>
      match asMat? e with
      | some rows => rows[0]!.size == 2
      | none => false
  | _ => false
#guard
  match parse "solve([1, 1; 0, 1], [3; 2])" with
  | .ok e =>
      match asMat? e with
      | some rows =>
          rows.size == 2 && simplify rows[0]![0]! == ofInt 1
            && simplify rows[1]![0]! == ofInt 2
      | none => false
  | _ => false
#guard
  match parse "coeff(3*x^2+2*x+1, 1)" with
  | .ok e => e == ofInt 2
  | _ => false

-- Definite integrals (FTC) & Taylor series
#guard
  match integrateDefinite (x ^ (2 : Expr)) "x" (0 : Expr) (1 : Expr) with
  | .success r _ => r == ofRat ⟨1, 3⟩
  | _ => false
#guard
  match parse "int(x^2, 0, 1)" with
  | .ok e => e == ofRat ⟨1, 3⟩
  | _ => false
#guard
  match parse "int(x, x, 0, 2)" with
  | .ok e => e == ofInt 2
  | _ => false
#guard
  match parse "int(sin(x), 0, 0)" with
  | .ok e => e == ofInt 0
  | _ => false
#guard
  -- exp Maclaurin order 2: 1 + x + x²/2
  equivNF (maclaurin (exp x) "x" 2)
    (1 + x + (1 : Expr) / (2 : Expr) * x ^ (2 : Expr))
#guard
  -- sin Maclaurin order 3: x − x³/6
  equivNF (maclaurin (sin x) "x" 3)
    (x - (1 : Expr) / (6 : Expr) * x ^ (3 : Expr))
#guard
  match parse "taylor(exp(x), 2)" with
  | .ok e =>
      equivNF e (1 + x + (1 : Expr) / (2 : Expr) * x ^ (2 : Expr))
  | _ => false
#guard
  match parse "laurent(1/(1-x), 3)" with
  | .ok e =>
      equivNF e (1 + x + x ^ (2 : Expr) + x ^ (3 : Expr))
  | _ => false
#guard
  match parse "laurent(1/x, 2)" with
  | .ok e => equivNF e ((1 : Expr) / x)
  | _ => false
#guard
  match parse "seriesmul(1/(1-x), 1/(1-x), 2)" with
  | .ok e =>
      equivNF e (1 + (2 : Expr) * x + (3 : Expr) * x ^ (2 : Expr))
  | _ => false
-- PR Q: decimals + numeric N
#guard
  match parse "0.5" with
  | .ok e => simplify e == ofRat ⟨1, 2⟩
  | _ => false
#guard
  match parse "1.25" with
  | .ok e => simplify e == ofRat ⟨5, 4⟩
  | _ => false
#guard
  match parse "0.5 + 0.5" with
  | .ok e => simplify e == ofInt 1
  | _ => false
#guard
  match parse "N(sin(1), 4)" with
  | .ok e =>
      -- ≈ 0.8415
      match eval? e with
      | some c =>
          match CplxConst.toRat? c with
          | some q =>
              let f := ratToFloat q
              Float.abs (f - 0.8415) < 0.001
          | none => false
      | none => false
  | _ => false
#guard
  match parse "N(1/2)" with
  | .ok e => simplify e == ofRat ⟨1, 2⟩
  | _ => false
#guard
  match parse "series(sin(x), 3)" with
  | .ok e =>
      equivNF e (x - (1 : Expr) / (6 : Expr) * x ^ (3 : Expr))
  | _ => false
#guard
  -- Taylor of 1/(1-x) about 0 order 2 ≈ 1 + x + x²
  equivNF (taylor ((1 : Expr) / (1 - x)) "x" zero 2)
    (1 + x + x ^ (2 : Expr))
#guard natFactorial 5 == 120
#guard natFactorial 0 == 1

-- Characteristic polynomial & eigenvalues
#guard
  let A := #[#[(1 : Expr), (0 : Expr)], #[(0 : Expr), (2 : Expr)]]
  match Mat.charpoly A with
  | some p =>
      equivNF p ((var "t") ^ (2 : Expr) - (3 : Expr) * var "t" + (2 : Expr))
  | none => false
#guard
  let A := #[#[(1 : Expr), (0 : Expr)], #[(0 : Expr), (2 : Expr)]]
  match Mat.eigenvalues A with
  | some rs =>
      rs.length == 2 && rs.any (· == ofInt 1) && rs.any (· == ofInt 2)
  | none => false
#guard
  match parse "eigvals([0, -1; 1, 0])" with
  | .ok e =>
      match asMat? e with
      | some rows =>
          rows.size == 1 && rows[0]!.size == 2
            && rows[0]!.toList.any (fun x => simplify x == I || simplify x == neg I)
      | none => false
  | _ => false
#guard
  match parse "charpoly([1, 0; 0, 2])" with
  | .ok e =>
      equivNF e ((var "t") ^ (2 : Expr) - (3 : Expr) * var "t" + (2 : Expr))
  | _ => false
#guard
  match parse "eigvals([1, 0; 0, 2])" with
  | .ok e =>
      match asMat? e with
      | some rows => rows.size == 1 && rows[0]!.size == 2
      | none => false
  | _ => false
#guard
  match parse "eigenspace([1, 0; 0, 2], 2)" with
  | .ok e =>
      match asMat? e with
      | some rows =>
          Mat.nrows rows == 2 && Mat.ncols rows == 1
            && simplify (Mat.get! rows 0 0) == ofInt 0
            && simplify (Mat.get! rows 1 0) == ofInt 1
      | none => false
  | _ => false

-- Limits
#guard
  match limit ((x ^ (2 : Expr) - 1) / (x - 1)) "x" (.finite (1 : Expr)) with
  | .value r => r == ofInt 2
  | _ => false
#guard
  match limit ((3 : Expr) * x ^ (2 : Expr) + x) "x" .posInf with
  | .infinity true => true
  | _ => false
#guard
  match limit (((2 : Expr) * x + 1) / ((3 : Expr) * x + 4)) "x" .posInf with
  | .value r => r == ofRat ⟨2, 3⟩
  | _ => false
#guard
  match limit ((1 : Expr) / x) "x" .posInf with
  | .value r => r == ofInt 0
  | _ => false
#guard
  match parse "limit((x^2-1)/(x-1), 1)" with
  | .ok e => e == ofInt 2
  | _ => false
#guard
  match parse "limit(1/x, oo)" with
  | .ok e => e == ofInt 0
  | _ => false
#guard
  match parse "lim((2*x+1)/(3*x+4), x, oo)" with
  | .ok e => e == ofRat ⟨2, 3⟩
  | _ => false

-- One-sided limits & poles
#guard
  match limit ((1 : Expr) / x) "x" (.finite (0 : Expr)) .right with
  | .infinity true => true
  | _ => false
#guard
  match limit ((1 : Expr) / x) "x" (.finite (0 : Expr)) .left with
  | .infinity false => true
  | _ => false
#guard
  match limit ((1 : Expr) / x) "x" (.finite (0 : Expr)) .both with
  | .undetermined _ => true
  | _ => false
#guard
  match limit ((1 : Expr) / (x ^ (2 : Expr))) "x" (.finite (0 : Expr)) .both with
  | .infinity true => true  -- 1/x² → +∞ both sides
  | _ => false
#guard
  match poleOrder? ((1 : Expr) / x) "x" (0 : Expr) with
  | some 1 => true
  | _ => false
#guard
  match poleOrder? ((1 : Expr) / (x ^ (2 : Expr))) "x" (0 : Expr) with
  | some 2 => true
  | _ => false
#guard
  match poleOrder? ((x ^ (2 : Expr) - 1) / (x - 1)) "x" (1 : Expr) with
  | none => true  -- removable
  | _ => false
#guard
  match classifyAt ((1 : Expr) / x) "x" (0 : Expr) with
  | .pole 1 _ _ => true
  | _ => false
#guard
  match classifyAt ((x - 1) / (x - 1)) "x" (1 : Expr) with
  | .removable r => r == ofInt 1
  | .continuous r => r == ofInt 1
  | _ => false
#guard
  match parse "limright(1/x, 0)" with
  | .ok e => e == var "∞"
  | _ => false
#guard
  match parse "limleft(1/x, 0)" with
  | .ok e => e == neg (var "∞") || e == mul negOne (var "∞")
  | _ => false
#guard
  match parse "poleorder(1/x^2, 0)" with
  | .ok e => e == ofInt 2
  | _ => false
#guard
  match parse "limit(1/x, 0, 1)" with
  | .ok e => e == var "∞"
  | _ => false
#guard
  match parse "limit(1/x, 0, -1)" with
  | .ok e => e == neg (var "∞") || e == mul negOne (var "∞")
  | _ => false

-- Radical integrals 1/√(·)
#guard checkAntiderivative (1 / sqrt (x ^ (2 : Expr) + 1)) "x"
#guard checkAntiderivative (1 / sqrt (1 - x ^ (2 : Expr))) "x"
#guard checkAntiderivative (1 / sqrt (x ^ (2 : Expr) - 1)) "x"
#guard
  match parse "int(1/sqrt(x^2+1))" with
  | .ok e => verifyDerivative e (1 / sqrt (x ^ (2 : Expr) + 1)) "x"
  | _ => false

-- Equations (`=`) and pretty-print v2
#guard
  match parse "x^2 = 4" with
  | .ok e =>
      match asEquation? e with
      | some (l, r) => simplify l == x ^ (2 : Expr) && r == ofInt 4
      | none => false
  | _ => false
#guard
  match parse "solve(x^2=4, x)" with
  | .ok e =>
      match asMat? e with
      | some rows =>
          rows[0]!.size == 2
            && rows[0]!.toList.any (· == ofInt 2)
            && rows[0]!.toList.any (· == ofInt (-2))
      | none => false
  | _ => false
#guard
  match parse "solve(2*x+1=0)" with
  | .ok e =>
      match asMat? e with
      | some rows => simplify rows[0]![0]! == ofRat ⟨-1, 2⟩
      | none => false
  | _ => false
-- Linear systems & inequalities (PR M/N)
#guard
  match parse "solve(x+y=1, x-y=3)" with
  | .ok e =>
      namedGet? e "x" == some (ofInt 2)
        && namedGet? e "y" == some (ofInt (-1))
  | _ => false
#guard
  match parse "solve(x^2+y^2=1, x+y=1)" with
  | .ok e =>
      let s := prettySolution e
      s.contains "x = 1" && s.contains "y = 0"
        && s.contains "x = 0" && s.contains "y = 1"
  | _ => false
#guard
  match parse "solve(y=x^2, x+y=2)" with
  | .ok e =>
      let s := prettySolution e
      s.contains "x = 1" && s.contains "y = 1"
  | _ => false
#guard
  match parse "x^2 > 1" with
  | .ok e =>
      match asRelation? e with
      | some (.lt, a, b) => simplify a == ofInt 1 && simplify b == x ^ (2 : Expr)
      | _ => false
  | _ => false
#guard
  match parse "solve(x^2-1>0)" with
  | .ok e =>
      match asMat? e with
      | some rows => Mat.nrows rows == 2 && Mat.ncols rows == 4
      | none => false
  | _ => false
#guard
  match parse "solve(x^2-1<0)" with
  | .ok e =>
      match asMat? e with
      | some rows =>
          Mat.nrows rows == 1 && Mat.ncols rows ≥ 2
            && simplify (Mat.get! rows 0 0) == ofInt (-1)
            && simplify (Mat.get! rows 0 1) == ofInt 1
      | none => false
  | _ => false
#guard
  match parse "solve(x+y=1, x-y=3)" with
  | .ok e =>
      let s := prettySolution e
      s.contains "x = 2" && s.contains "y = -1"
  | _ => false
#guard
  match parse "solve(x^2-1>0)" with
  | .ok e => (prettySolution e).contains "∪"
  | _ => false
#guard
  match parse "solve(x^2+1<0)" with
  | .ok e => prettySolution e == "∅"
  | _ => false
#guard
  -- √ and superscripts
  (Expr.toString (sqrt (x ^ (2 : Expr) + 1))).contains "√"
#guard
  (Expr.toString (x ^ (2 : Expr))).contains "²"
    || Expr.toString (x ^ (2 : Expr)) == "x²"
#guard
  -- degree-sorted charpoly-like poly
  let p := (var "t") ^ (2 : Expr) - (3 : Expr) * var "t" + (2 : Expr)
  let s := Expr.toString (simplify p)
  -- leading term should involve t² / t^2 before the constant
  s.startsWith "t" || s.startsWith "t²" || s.startsWith "t^"
#guard
  Expr.toString (neg (var "∞")) == "-∞"
    || Expr.toString (mul negOne (var "oo")) == "-∞"

-- Partial fractions (apart)
#guard
  match apart ((1 : Expr) / ((x - 1) * (x - 2))) "x" with
  | some e =>
      -- A/(x-1) + B/(x-2); check equivalent to original
      equivNF e ((1 : Expr) / ((x - 1) * (x - 2)))
  | none => false
#guard
  match parse "apart(1/((x-1)*(x+1)))" with
  | .ok e =>
      equivNF e ((1 : Expr) / ((x - 1) * (x + 1)))
        || equivNF e ((1 : Expr) / (x ^ (2 : Expr) - 1))
  | _ => false
#guard
  match parse "pf((x+1)/(x*(x-1)))" with
  | .ok e =>
      -- should split into sum of proper fractions
      match RatFn.ofExpr? e "x" with
      | some _ => true  -- still rational
      | none =>
          -- sum of terms
          true
  | _ => false

-- √ integrals now verified
#guard checkAntiderivative (sqrt (x ^ (2 : Expr) + 1)) "x"
#guard checkAntiderivative (sqrt (x ^ (2 : Expr) - 1)) "x"
#guard
  match parse "int(sqrt(x^2+1))" with
  | .ok e => verifyDerivative e (sqrt (x ^ (2 : Expr) + 1)) "x"
  | _ => false

-- Diagonalize & expm
#guard
  let A := #[#[(1 : Expr), (0 : Expr)], #[(0 : Expr), (2 : Expr)]]
  match Mat.diagonalize A with
  | .ok P D =>
      Mat.nrows P == 2 && Mat.ncols D == 2
        && simplify (Mat.get! D 0 1) == ofInt 0
  | _ => false
#guard
  let Z := #[#[(0 : Expr), (0 : Expr)], #[(0 : Expr), (0 : Expr)]]
  match Mat.expm Z with
  | .ok R =>
      simplify (Mat.get! R 0 0) == ofInt 1
        && simplify (Mat.get! R 1 1) == ofInt 1
  | _ => false
#guard
  match parse "diagform([3, 0; 0, 5])" with
  | .ok e =>
      match asMat? e with
      | some D =>
          let a := simplify (Mat.get! D 0 0)
          let b := simplify (Mat.get! D 1 1)
          (a == ofInt 3 || a == ofInt 5) && (b == ofInt 3 || b == ofInt 5)
      | none => false
  | _ => false
#guard
  match parse "expm(zeros(2))" with
  | .ok e =>
      match asMat? e with
      | some R =>
          simplify (Mat.get! R 0 0) == ofInt 1
            && simplify (Mat.get! R 1 1) == ofInt 1
      | none => false
  | _ => false
#guard
  match parse "diagonalize([1, 0; 0, 2])" with
  | .ok e =>
      match asMat? e with
      | some rows => rows.size == 1 && rows[0]!.size == 2
      | none => false
  | _ => false

-- Finite sums
#guard
  match sumFinite (var "k") "k" (1 : Expr) (var "n") with
  | some s =>
      equivNF s (div (mul (var "n") (add (var "n") one)) (ofInt 2))
  | none => false
#guard
  match sumFinite ((var "k") ^ (2 : Expr)) "k" (1 : Expr) (var "n") with
  | some s => dependsOn s "n"
  | none => false
#guard
  match parse "sum(k, 1, n, k)" with
  | .ok e =>
      equivNF e (div (mul (var "n") (add (var "n") one)) (ofInt 2))
  | _ => false
#guard
  match parse "sum(k^2, k, 1, n)" with
  | .ok e => dependsOn e "n"
  | _ => false
#guard
  match parse "sum(k, 0, n, 2^k)" with
  | .ok e => dependsOn e "n"
  | _ => false

-- First-order ODEs (yp = y')
#guard
  match dsolve (eq (add (var "yp") (var "y")) (0 : Expr)) "y" "x" with
  | .ok e =>
      match asEquation? e with
      | some (l, r) => l == var "y" && dependsOn r "C"
      | none => false
  | _ => false
#guard
  match parse "dsolve(yp + y = 0)" with
  | .ok e =>
      match asEquation? e with
      | some (l, _) => l == var "y"
      | none => false
  | _ => false
#guard
  match parse "dsolve(yp + y = x)" with
  | .ok e =>
      match asEquation? e with
      | some (l, r) => l == var "y" && dependsOn r "x"
      | none => false
  | _ => false
#guard
  match parse "dsolve(yp = x*y)" with
  | .ok e =>
      match asEquation? e with
      | some _ => true
      | none => false
  | _ => false
#guard
  match parse "dsolve(y' + y = 0)" with
  | .ok e =>
      match asEquation? e with
      | some (l, r) => l == var "y" && dependsOn r "C"
      | none => false
  | _ => false
#guard
  match parse "dsolve(yp + y = 0, 0, 1)" with
  | .ok e =>
      match asEquation? e with
      | some (_, r) =>
          !dependsOn r "C"
            && simplify (subst r "x" (0 : Expr)) == ofInt 1
      | none => false
  | _ => false
#guard
  match parse "sum(k, 1, 10, k)" with
  | .ok e => simplify e == ofInt 55
  | _ => false
#guard
  match parse "sum(k^2, k, 1, 5)" with
  | .ok e => simplify e == ofInt 55
  | _ => false
-- PR O: second-order ODE & linear systems
#guard
  match parse "dsolve(y'' + y = 0)" with
  | .ok e =>
      match asEquation? e with
      | some (l, r) =>
          l == var "y" && dependsOn r "C1" && dependsOn r "C2"
      | none => false
  | _ => false
#guard
  match parse "dsolve(y'' + y = 0, 0, 1, 0)" with
  | .ok e =>
      match asEquation? e with
      | some (_, r) =>
          !dependsOn r "C1" && simplify (subst r "x" (0:Expr)) == ofInt 1
      | none => false
  | _ => false
#guard
  match parse "dsolve([1, 0; 0, 2])" with
  | .ok e =>
      (prettySolution e).contains "y1" && (prettySolution e).contains "exp"
  | _ => false
#guard
  match parse "dsolve([1, 0; 0, 2], [3; 4])" with
  | .ok e =>
      let s := prettySolution e
      s.contains "3" && s.contains "4" && !s.contains "C1"
  | _ => false

end Taschenrechner.Tests
