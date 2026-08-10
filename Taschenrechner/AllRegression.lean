/-
  Master regression runner: integration, matrix, limits, solve/algebra, sum/ODE.

  CLI: `lake exe taschenrechner --all-regression`
-/
import Taschenrechner.Regression
import Taschenrechner.MatrixRegression
import Taschenrechner.LimitRegression
import Taschenrechner.SolveRegression
import Taschenrechner.SumODERegression

namespace Taschenrechner.AllRegression

open Taschenrechner

structure SuiteSummary where
  name    : String
  passed  : Nat
  total   : Nat
  deriving Repr

def summary (name : String) (passed total : Nat) : SuiteSummary :=
  { name, passed, total }

def formatSummary (s : SuiteSummary) : String :=
  let mark := if s.passed == s.total then "✓" else "✗"
  s!"  {mark}  {s.name}: {s.passed}/{s.total}"

/-- Run every domain suite; exit 0 iff all cases pass. -/
def runSuiteIO : IO UInt32 := do
  IO.println "═══════════════════════════════════════════════"
  IO.println "  Taschenrechner — full cross-domain regression"
  IO.println "═══════════════════════════════════════════════"
  IO.println ""

  let intR := Regression.runSuite
  let matR := MatrixRegression.runSuite
  let limR := LimitRegression.runSuite
  let solR := SolveRegression.runSuite
  let sumR := SumODERegression.runSuite

  IO.println (Regression.formatReport intR)
  IO.println ""
  IO.println (MatrixRegression.formatReport matR)
  IO.println ""
  IO.println (LimitRegression.formatReport limR)
  IO.println ""
  IO.println (SolveRegression.formatReport solR)
  IO.println ""
  IO.println (SumODERegression.formatReport sumR)
  IO.println ""

  let summaries := [
    summary "integration" (Regression.passCount intR) intR.length,
    summary "matrix" (MatrixRegression.passCount matR) matR.length,
    summary "limits" (LimitRegression.passCount limR) limR.length,
    summary "solve/algebra" (SolveRegression.passCount solR) solR.length,
    summary "sum/ODE" (SumODERegression.passCount sumR) sumR.length
  ]

  let totalPass := summaries.foldl (fun a s => a + s.passed) 0
  let totalAll := summaries.foldl (fun a s => a + s.total) 0

  IO.println "── Summary ──────────────────────────────────"
  for s in summaries do
    IO.println (formatSummary s)
  IO.println s!"  total: {totalPass}/{totalAll}"
  IO.println ""

  if totalPass == totalAll then
    IO.println "All cross-domain regression cases passed."
    pure 0
  else
    IO.println "Cross-domain regression failures detected."
    pure 1

/-- Compile-time: every suite green. -/
def allGreen : Bool :=
  Regression.allPassed (Regression.runSuite)
    && MatrixRegression.allPassed (MatrixRegression.runSuite)
    && LimitRegression.allPassed (LimitRegression.runSuite)
    && SolveRegression.allPassed (SolveRegression.runSuite)
    && SumODERegression.allPassed (SumODERegression.runSuite)

#guard allGreen

end Taschenrechner.AllRegression
