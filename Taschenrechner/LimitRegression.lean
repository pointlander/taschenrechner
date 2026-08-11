/-
  Limit / pole-classification regression suite.

  Run at compile time via `#guard` and from the CLI with
  `lake exe taschenrechner --limit-regression`.
-/
import Taschenrechner.Parse
import Taschenrechner.Simplify
import Taschenrechner.Normal
import Taschenrechner.Limit
import Taschenrechner.Matrix
import Taschenrechner.Expr

namespace Taschenrechner.LimitRegression

open Taschenrechner
open Taschenrechner.Expr
open Taschenrechner.Parse

structure Case where
  name  : String
  input : String
  check : Expr → Bool

def parseE (s : String) : Option Expr :=
  match parse s with
  | .ok e => some (simplify e)
  | .error _ => none

def isInfPos (e : Expr) : Bool :=
  match e with
  | var v => isInfName v
  | _ => false

def isInfNeg (e : Expr) : Bool :=
  match e with
  | mul (const c) (var v) => c.isNegOne && isInfName v
  | _ =>
    -- neg ∞ after simplify
    simplify e == simplify (neg (var "∞"))
      || simplify e == simplify (mul negOne (var "∞"))
      || simplify e == simplify (mul negOne (var "oo"))

def suite : List Case := [
  { name := "removable (x²−1)/(x−1) → 2"
    input := "limit((x^2-1)/(x-1), 1)"
    check := fun e => simplify e == ofInt 2 },
  { name := "1/x → 0 at +∞"
    input := "limit(1/x, oo)"
    check := fun e => simplify e == ofInt 0 },
  { name := "ratio of linears at +∞"
    input := "lim((2*x+1)/(3*x+4), oo)"
    check := fun e => simplify e == ofRat ⟨2, 3⟩ },
  { name := "poly → +∞ at +∞"
    input := "limit(x^2, oo)"
    check := fun e => isInfPos e },
  { name := "poly → −∞ at −∞"
    input := "limit(x^3, -oo)"
    check := fun e => isInfNeg e },
  { name := "limright 1/x at 0 → +∞"
    input := "limright(1/x, 0)"
    check := fun e => isInfPos e },
  { name := "limleft 1/x at 0 → −∞"
    input := "limleft(1/x, 0)"
    check := fun e => isInfNeg e },
  { name := "1/x² both sides +∞"
    input := "limit(1/x^2, 0)"
    check := fun e => isInfPos e },
  { name := "poleorder 1/x at 0"
    input := "poleorder(1/x, 0)"
    check := fun e => simplify e == ofInt 1 },
  { name := "poleorder 1/x² at 0"
    input := "poleorder(1/x^2, 0)"
    check := fun e => simplify e == ofInt 2 },
  { name := "poleorder removable → 0"
    input := "poleorder((x^2-1)/(x-1), 1)"
    check := fun e => simplify e == ofInt 0 },
  { name := "classify 1/x pole shape"
    input := "classify(1/x, 0)"
    check := fun e =>
      match asMat? e with
      | some rows =>
          Mat.nrows rows == 1 && Mat.ncols rows == 3
            && simplify (Mat.get! rows 0 0) == ofInt 1
      | none => false },
  { name := "classify removable → 2"
    input := "classify((x^2-1)/(x-1), 1)"
    check := fun e => simplify e == ofInt 2 },
  { name := "limit side 1 = right"
    input := "limit(1/x, 0, 1)"
    check := fun e => isInfPos e },
  { name := "limit side -1 = left"
    input := "limit(1/x, 0, -1)"
    check := fun e => isInfNeg e },
  -- PR P: Laurent series & series arithmetic
  { name := "laurent 1/x"
    input := "laurent(1/x, 2)"
    check := fun e => equivNF e ((1 : Expr) / x) },
  { name := "laurent 1/x²"
    input := "laurent(1/x^2, 1)"
    check := fun e => equivNF e ((1 : Expr) / (x ^ (2 : Expr))) },
  { name := "laurent geometric 1/(1-x)"
    input := "laurent(1/(1-x), 3)"
    check := fun e =>
      equivNF e (1 + x + x ^ (2 : Expr) + x ^ (3 : Expr)) },
  { name := "laurent about a=1"
    input := "laurent(1/(x-1), 1, 2)"
    check := fun e => equivNF e ((1 : Expr) / (x - 1)) },
  { name := "laurent removable → Taylor"
    input := "laurent((x^2-1)/(x-1), 1, 2)"
    check := fun e => equivNF e (x + 1) },
  { name := "seriesmul 1/(1-x)² coeffs"
    input := "seriesmul(1/(1-x), 1/(1-x), 3)"
    check := fun e =>
      -- 1 + 2x + 3x² + 4x³
      equivNF e (1 + (2 : Expr) * x + (3 : Expr) * x ^ (2 : Expr)
        + (4 : Expr) * x ^ (3 : Expr)) },
  { name := "seriesadd 1/x + 1/(1-x)"
    input := "seriesadd(1/x, 1/(1-x), 2)"
    check := fun e =>
      equivNF e ((1 : Expr) / x + 1 + x + x ^ (2 : Expr)) },
  { name := "taylor still works"
    input := "taylor(exp(x), 2)"
    check := fun e =>
      equivNF e (1 + x + (1 : Expr) / (2 : Expr) * x ^ (2 : Expr)) }
]

structure CaseResult where
  name   : String
  passed : Bool
  detail : String
  deriving Repr

def runCase (c : Case) : CaseResult :=
  match parseE c.input with
  | none => { name := c.name, passed := false, detail := "parse/eval failed" }
  | some e =>
    let ok := c.check e
    { name := c.name
      passed := ok
      detail := if ok then s!"ok → {e}" else s!"check failed → {e}" }

def runSuite (cases : List Case := suite) : List CaseResult :=
  cases.map runCase

def allPassed (results : List CaseResult := runSuite) : Bool :=
  results.all (·.passed)

def passCount (results : List CaseResult) : Nat :=
  results.filter (·.passed) |>.length

def formatReport (results : List CaseResult) : String :=
  let total := results.length
  let n := passCount results
  let lines :=
    results.map fun r =>
      let mark := if r.passed then "✓" else "✗"
      s!"  {mark}  {r.name}: {r.detail}"
  String.intercalate "\n" (s!"Limit/series regression: {n}/{total} passed" :: lines)

def runSuiteIO : IO UInt32 := do
  let results := runSuite
  IO.println (formatReport results)
  if allPassed results then
    IO.println "All limit regression cases passed."
    pure 0
  else
    IO.println "Limit regression failures detected."
    pure 1

#guard allPassed (runSuite suite)
#guard suite.length ≥ 20

end Taschenrechner.LimitRegression
