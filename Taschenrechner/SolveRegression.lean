/-
  Algebra regression: factor, roots, solve, apart, normal forms.

  Run at compile time via `#guard` and from the CLI with
  `lake exe taschenrechner --solve-regression`.
-/
import Taschenrechner.Parse
import Taschenrechner.Simplify
import Taschenrechner.Normal
import Taschenrechner.Solve
import Taschenrechner.Matrix
import Taschenrechner.Expr

namespace Taschenrechner.SolveRegression

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

def isRow (e : Expr) (n : Nat) : Bool :=
  match asMat? e with
  | some rows => Mat.nrows rows == 1 && Mat.ncols rows == n
  | none => false

def rowContains (e : Expr) (vals : List Expr) : Bool :=
  match asMat? e with
  | none => false
  | some rows =>
      if rows.isEmpty then false
      else
        let entries := rows[0]!.toList.map simplify
        vals.all fun v => entries.any (· == simplify v)

def suite : List Case := [
  { name := "solve x²=4"
    input := "solve(x^2=4, x)"
    check := fun e => isRow e 2 && rowContains e [ofInt 2, ofInt (-2)] },
  { name := "solve 2x+1=0"
    input := "solve(2*x+1=0)"
    check := fun e => isRow e 1 && rowContains e [ofRat ⟨-1, 2⟩] },
  { name := "solve quadratic"
    input := "solve(x^2-5*x+6=0, x)"
    check := fun e => isRow e 2 && rowContains e [ofInt 2, ofInt 3] },
  { name := "roots x²−1"
    input := "roots(x^2-1)"
    check := fun e => isRow e 2 && rowContains e [ofInt 1, ofInt (-1)] },
  { name := "factor x²−1"
    input := "factor(x^2-1)"
    check := fun e =>
      equivNF e ((x - 1) * (x + 1)) },
  { name := "factor x²−5x+6"
    input := "factor(x^2-5*x+6)"
    check := fun e =>
      equivNF e ((x - 2) * (x - 3))
        || equivNF e ((x - 3) * (x - 2)) },
  { name := "apart 1/((x-1)(x-2))"
    input := "apart(1/((x-1)*(x-2)))"
    check := fun e =>
      equivNF e ((1 : Expr) / ((x - 1) * (x - 2))) },
  { name := "apart 1/(x²−1)"
    input := "apart(1/(x^2-1))"
    check := fun e =>
      equivNF e ((1 : Expr) / (x ^ (2 : Expr) - 1)) },
  { name := "nf 1/x+2/x"
    input := "nf(1/x + 2/x)"
    check := fun e => equivNF e ((3 : Expr) / x) },
  { name := "cancel (x²−1)/(x−1)"
    input := "cancel((x^2-1)/(x-1))"
    check := fun e => equivNF e (x + 1) },
  { name := "coeff of x²"
    input := "coeff(3*x^2+2*x+1, 2)"
    check := fun e => simplify e == ofInt 3 },
  { name := "collect (x+1)²"
    input := "collect((x+1)^2)"
    check := fun e =>
      equivNF e (x ^ (2 : Expr) + (2 : Expr) * x + 1) },
  { name := "subst x²+1 at 3"
    input := "subst(x^2+1, x, 3)"
    check := fun e => simplify e == ofInt 10 },
  { name := "eval x²+1 at 4"
    input := "eval(x^2+1, x, 4)"
    check := fun e => simplify e == ofInt 17 },
  { name := "matrix solve still works"
    input := "solve([1, 1; 0, 1], [3; 2])"
    check := fun e =>
      match asMat? e with
      | some rows =>
          Mat.nrows rows == 2
            && simplify (Mat.get! rows 0 0) == ofInt 1
            && simplify (Mat.get! rows 1 0) == ofInt 2
      | none => false }
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
  String.intercalate "\n" (s!"Solve/algebra regression: {n}/{total} passed" :: lines)

def runSuiteIO : IO UInt32 := do
  let results := runSuite
  IO.println (formatReport results)
  if allPassed results then
    IO.println "All solve/algebra regression cases passed."
    pure 0
  else
    IO.println "Solve/algebra regression failures detected."
    pure 1

#guard allPassed (runSuite suite)
#guard suite.length ≥ 12

end Taschenrechner.SolveRegression
