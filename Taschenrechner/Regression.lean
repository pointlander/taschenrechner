/-
  Integration regression suite (polynomials, Risch, trig, radicals, …).

  Each case records an integrand string (parsed) and an expected outcome.
  Run at compile time via `#guard` and from the CLI with `--regression`.
  Full cross-domain run: `--all-regression`.
-/
import Taschenrechner.Integrate
import Taschenrechner.Parse
import Taschenrechner.Risch

namespace Taschenrechner.Regression

open Taschenrechner
open Taschenrechner.Expr
open Taschenrechner.Parse

/-- Expected outcome for a regression case. -/
inductive Expect where
  /-- Verified elementary antiderivative (any source). -/
  | elementary
  /-- Verified elementary from Risch specifically. -/
  | risch
  /-- Verified elementary from heuristic specifically. -/
  | heuristic
  /-- Risch (or integrate) reports non-existence. -/
  | notElementary
  /-- Must fail to integrate (and must not claim success). -/
  | fails
  deriving Repr, BEq

structure Case where
  name      : String
  integrand : String
  var       : String := "x"
  expect    : Expect
  deriving Repr

/-- Canonical integration suite (polynomials, Risch, trig, radicals, K(x)). -/
def suite : List Case := [
  -- 1–5: polynomials / rationals (Risch)
  { name := "poly x^2",           integrand := "x^2",                 expect := .risch },
  { name := "poly 3x+1",          integrand := "3*x + 1",             expect := .risch },
  { name := "1/x",                integrand := "1/x",                 expect := .risch },
  { name := "1/(x^2+1)",          integrand := "1/(x^2+1)",           expect := .risch },
  { name := "d/dx log quadratic", integrand := "(2*x+1)/(x^2+x+1)",  expect := .risch },
  -- 6–10: exp (Risch DE)
  { name := "exp(x)",             integrand := "exp(x)",              expect := .risch },
  { name := "exp(2x)",            integrand := "exp(2*x)",            expect := .risch },
  { name := "exp(3x)",            integrand := "exp(3*x)",            expect := .risch },
  { name := "x*exp(x)",           integrand := "x*exp(x)",            expect := .risch },
  { name := "x*exp(x^2)",         integrand := "x*exp(x^2)",          expect := .risch },
  -- 11–12: non-elementary certificates
  { name := "exp(x^2) NE",        integrand := "exp(x^2)",            expect := .notElementary },
  { name := "exp(x^3) NE",        integrand := "exp(x^3)",            expect := .notElementary },
  -- 13–16: rational more
  { name := "1/(x-1)",            integrand := "1/(x-1)",             expect := .risch },
  { name := "x^3/(x+1)",          integrand := "x^3/(x+1)",           expect := .risch },
  { name := "x/(x^2+1)",          integrand := "x/(x^2+1)",           expect := .elementary },
  { name := "2/x",                integrand := "2/x",                 expect := .risch },
  -- 17–20: trig via Risch preprocessing (linear args)
  { name := "sin(x)",             integrand := "sin(x)",              expect := .risch },
  { name := "cos(2x)",            integrand := "cos(2*x)",            expect := .risch },
  { name := "2x cos(x^2)",        integrand := "2*x*cos(x^2)",        expect := .heuristic },
  { name := "ln(x)",              integrand := "ln(x)",               expect := .elementary },
  -- 21–30: more trig / product-to-sum (Risch)
  { name := "cos(x)",             integrand := "cos(x)",              expect := .risch },
  { name := "sin(3x)",            integrand := "sin(3*x)",            expect := .risch },
  { name := "tan(x)",             integrand := "tan(x)",              expect := .risch },
  { name := "tan(2x)",            integrand := "tan(2*x)",            expect := .risch },
  { name := "3*sin(x)",           integrand := "3*sin(x)",            expect := .risch },
  { name := "sin(x)+cos(x)",      integrand := "sin(x)+cos(x)",       expect := .risch },
  { name := "sin(x)*cos(x)",      integrand := "sin(x)*cos(x)",       expect := .risch },
  { name := "sin(x)^2",           integrand := "sin(x)^2",            expect := .risch },
  { name := "cos(x)^2",           integrand := "cos(x)^2",            expect := .risch },
  { name := "sin(2x)+1",          integrand := "sin(2*x)+1",          expect := .risch },
  -- 31–40: mix of rational, exp, heuristic, NE
  { name := "cos(x/2)",           integrand := "cos(x/2)",            expect := .risch },
  { name := "(x+1)^2",            integrand := "(x+1)^2",             expect := .elementary },
  { name := "exp(-x)",            integrand := "exp(-x)",             expect := .risch },
  { name := "4*exp(x)",           integrand := "4*exp(x)",            expect := .risch },
  { name := "1/(x^2+2*x+1)",      integrand := "1/(x^2+2*x+1)",       expect := .elementary },
  { name := "sin(x^2) chain",     integrand := "2*x*sin(x^2)",        expect := .heuristic },
  { name := "x*ln(x)",            integrand := "x*ln(x)",             expect := .elementary },
  { name := "exp(x)+sin(x)",      integrand := "exp(x)+sin(x)",       expect := .risch },
  { name := "cos(x)-sin(x)",      integrand := "cos(x)-sin(x)",       expect := .risch },
  { name := "x^2*exp(x^3)",       integrand := "x^2*exp(x^3)",        expect := .risch },
  -- radical table: 1/√ and √ (heuristic, verified)
  { name := "1/sqrt(x^2+1)",      integrand := "1/sqrt(x^2+1)",       expect := .heuristic },
  { name := "1/sqrt(1-x^2)",      integrand := "1/sqrt(1-x^2)",       expect := .heuristic },
  { name := "1/sqrt(x^2-1)",      integrand := "1/sqrt(x^2-1)",       expect := .heuristic },
  { name := "sqrt(x^2+1)",        integrand := "sqrt(x^2+1)",         expect := .heuristic },
  { name := "sqrt(x^2-1)",        integrand := "sqrt(x^2-1)",         expect := .heuristic },
  -- rational over K = ℚ(√2)
  { name := "1/(x-sqrt(2))",      integrand := "1/(x-sqrt(2))",       expect := .risch },
  { name := "(x+sqrt(2))/(x^2-2)", integrand := "(x+sqrt(2))/(x^2-2)", expect := .risch },
  { name := "1/(x^2-2)",          integrand := "1/(x^2-2)",           expect := .risch }
]

/-- Does a result match the expectation? -/
def expectOk (r : IntegrateResult) (ex : Expect) : Bool :=
  match ex, r with
  | .elementary,     .success _ _          => true
  | .risch,          .success _ .risch     => true
  | .heuristic,      .success _ .heuristic => true
  | .notElementary,  .notElementary _      => true
  | .fails,          .failure _            => true
  | .fails,          .notElementary _      => true
  | _,               _                     => false

structure CaseResult where
  name    : String
  passed  : Bool
  detail  : String
  deriving Repr

/-- Run one case: parse → integrate → check expectation (+ re-verify on success). -/
def runCase (c : Case) : CaseResult :=
  match parse c.integrand with
  | .error err =>
    { name := c.name, passed := false, detail := s!"parse error: {err}" }
  | .ok f =>
    let r := integrate f c.var
    let okExpect := expectOk r c.expect
    let okVerify :=
      match r with
      | .success F _ => verifyDerivative F f c.var
      | .notElementary _ => c.expect == .notElementary
      | .failure _ => c.expect == .fails || c.expect == .notElementary
    let passed := okExpect && okVerify
    let detail :=
      match r with
      | .success F src =>
        s!"∫ = {F}  [{src}, verified={verifyDerivative F f c.var}]"
      | .notElementary reason => s!"not elementary: {reason}"
      | .failure reason => s!"failure: {reason}"
    { name := c.name, passed, detail }

def runSuite (cases : List Case := suite) : List CaseResult :=
  cases.map runCase

def allPassed (results : List CaseResult := runSuite) : Bool :=
  results.all (·.passed)

def passCount (results : List CaseResult) : Nat :=
  results.filter (·.passed) |>.length

def formatReport (results : List CaseResult) : String :=
  let total := results.length
  let nPass := passCount results
  let lines :=
    results.map fun r =>
      let mark := if r.passed then "✓" else "✗"
      s!"  {mark}  {r.name}: {r.detail}"
  let header := s!"Regression: {nPass}/{total} passed"
  String.intercalate "\n" (header :: lines)

/-- IO runner for CLI. Exit code 0 iff all pass. -/
def runSuiteIO : IO UInt32 := do
  let results := runSuite
  IO.println (formatReport results)
  if allPassed results then
    IO.println "All regression cases passed."
    pure 0
  else
    IO.println "Regression failures detected."
    pure 1

-- Compile-time guard: full suite green
#guard allPassed (runSuite suite)
#guard suite.length ≥ 40

end Taschenrechner.Regression
