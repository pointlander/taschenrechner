/-
  Small matrix regression suite (RREF / solve / basic ops).

  Run at compile time via `#guard` and from the CLI with
  `lake exe taschenrechner --matrix-regression`.
-/
import Taschenrechner.Parse
import Taschenrechner.Matrix
import Taschenrechner.LinAlg
import Taschenrechner.Simplify

namespace Taschenrechner.MatrixRegression

open Taschenrechner
open Taschenrechner.Expr
open Taschenrechner.Parse

structure Case where
  name   : String
  input  : String
  /-- Predicate on the parsed+evaluated expression. -/
  check  : Expr → Bool

/-- Helper: parse input string to Expr. -/
def parseE (s : String) : Option Expr :=
  match parse s with
  | .ok e => some (simplify e)
  | .error _ => none

def isMat (e : Expr) (m n : Nat) : Bool :=
  match asMat? e with
  | some rows => Mat.nrows rows == m && Mat.ncols rows == n
  | none => false

def entryEq (e : Expr) (i j : Nat) (expected : Expr) : Bool :=
  match asMat? e with
  | some rows =>
      if i < Mat.nrows rows && j < Mat.ncols rows then
        simplify (Mat.get! rows i j) == simplify expected
      else false
  | none => false

def allEntries (e : Expr) (pred : Nat → Nat → Expr → Bool) : Bool :=
  match asMat? e with
  | none => false
  | some rows =>
      Id.run do
        for i in [:Mat.nrows rows] do
          for j in [:Mat.ncols rows] do
            if !pred i j (Mat.get! rows i j) then return false
        pure true

/-- Canonical small matrix suite. -/
def suite : List Case := [
  -- basic identity / shape
  { name := "eye(2) shape"
    input := "eye(2)"
    check := fun e => isMat e 2 2
      && entryEq e 0 0 (1 : Expr) && entryEq e 0 1 (0 : Expr)
      && entryEq e 1 0 (0 : Expr) && entryEq e 1 1 (1 : Expr) },
  { name := "det 2x2"
    input := "det([1, 2; 3, 4])"
    check := fun e => simplify e == ofInt (-2) },
  { name := "trace 2x2"
    input := "trace([1, 2; 3, 4])"
    check := fun e => simplify e == (5 : Expr) },
  { name := "transpose"
    input := "transpose([1, 2; 3, 4])"
    check := fun e => isMat e 2 2
      && entryEq e 0 0 (1 : Expr) && entryEq e 0 1 (3 : Expr)
      && entryEq e 1 0 (2 : Expr) && entryEq e 1 1 (4 : Expr) },
  { name := "matmul swap"
    input := "[1, 2; 3, 4] * [0, 1; 1, 0]"
    check := fun e => isMat e 2 2
      && entryEq e 0 0 (2 : Expr) && entryEq e 0 1 (1 : Expr)
      && entryEq e 1 0 (4 : Expr) && entryEq e 1 1 (3 : Expr) },
  -- RREF
  { name := "rref identity"
    input := "rref(eye(3))"
    check := fun e => isMat e 3 3
      && entryEq e 0 0 (1 : Expr) && entryEq e 1 1 (1 : Expr) && entryEq e 2 2 (1 : Expr) },
  { name := "rref simple"
    input := "rref([1, 2; 2, 4])"
    check := fun e =>
      -- row-equivalent to [1, 2; 0, 0]
      isMat e 2 2
        && entryEq e 0 0 (1 : Expr) && entryEq e 0 1 (2 : Expr)
        && entryEq e 1 0 (0 : Expr) && entryEq e 1 1 (0 : Expr) },
  { name := "rref 2x3"
    input := "rref([1, 2, 3; 2, 4, 8])"
    check := fun e =>
      isMat e 2 3
        && entryEq e 0 0 (1 : Expr)
        && entryEq e 1 0 (0 : Expr) },
  -- rank
  { name := "rank full"
    input := "rank([1, 2; 3, 4])"
    check := fun e => simplify e == (2 : Expr) },
  { name := "rank deficient"
    input := "rank([1, 2; 2, 4])"
    check := fun e => simplify e == (1 : Expr) },
  -- solve
  { name := "solve 2x2"
    input := "solve([1, 1; 0, 1], [3; 2])"
    check := fun e =>
      -- x + y = 3, y = 2 → x = 1, y = 2
      isMat e 2 1
        && entryEq e 0 0 (1 : Expr) && entryEq e 1 0 (2 : Expr) },
  { name := "solve identity"
    input := "solve(eye(2), [5; 7])"
    check := fun e =>
      isMat e 2 1
        && entryEq e 0 0 (5 : Expr) && entryEq e 1 0 (7 : Expr) },
  { name := "solve 3x3"
    input := "solve([1, 0, 0; 0, 1, 0; 0, 0, 1], [1; 2; 3])"
    check := fun e =>
      isMat e 3 1
        && entryEq e 0 0 (1 : Expr)
        && entryEq e 1 0 (2 : Expr)
        && entryEq e 2 0 (3 : Expr) },
  { name := "inv via solve consistency"
    input := "inv([2, 0; 0, 3])"
    check := fun e =>
      isMat e 2 2
        && entryEq e 0 0 (ofRat ⟨1, 2⟩)
        && entryEq e 1 1 (ofRat ⟨1, 3⟩) },
  { name := "scalar matrix"
    input := "2 * eye(2)"
    check := fun e =>
      isMat e 2 2
        && entryEq e 0 0 (2 : Expr) && entryEq e 1 1 (2 : Expr)
        && entryEq e 0 1 (0 : Expr) }
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
  String.intercalate "\n" (s!"Matrix regression: {n}/{total} passed" :: lines)

def runSuiteIO : IO UInt32 := do
  let results := runSuite
  IO.println (formatReport results)
  if allPassed results then
    IO.println "All matrix regression cases passed."
    pure 0
  else
    IO.println "Matrix regression failures detected."
    pure 1

#guard allPassed (runSuite suite)
#guard suite.length ≥ 10

end Taschenrechner.MatrixRegression
