/-
  Finite-sum and first-order ODE regression suite.

  Run at compile time via `#guard` and from the CLI with
  `lake exe taschenrechner --sum-ode-regression`.
-/
import Taschenrechner.Parse
import Taschenrechner.Simplify
import Taschenrechner.Normal
import Taschenrechner.Sum
import Taschenrechner.ODE
import Taschenrechner.Diff
import Taschenrechner.Expr

namespace Taschenrechner.SumODERegression

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

def isEqY (e : Expr) : Bool :=
  match asEquation? e with
  | some (l, _) => l == var "y"
  | none => false

def suite : List Case := [
  { name := "sum k = n(n+1)/2"
    input := "sum(k, 1, n, k)"
    check := fun e =>
      equivNF e (div (mul (var "n") (add (var "n") one)) (ofInt 2)) },
  { name := "sum k² Faulhaber"
    input := "sum(k^2, k, 1, n)"
    check := fun e => dependsOn e "n" },
  { name := "sum k³"
    input := "sum(k^3, k, 1, n)"
    check := fun e =>
      equivNF e (pow (div (mul (var "n") (add (var "n") one)) (ofInt 2)) (ofInt 2)) },
  { name := "sum constants"
    input := "sum(k, 1, n, 1)"
    check := fun e => equivNF e (var "n") },
  { name := "geometric 2^k"
    input := "sum(k, 0, n, 2^k)"
    check := fun e => dependsOn e "n" },
  { name := "sum index-first form"
    input := "sum(k, 1, n, k+1)"
    check := fun e => dependsOn e "n" },
  { name := "dsolve yp+y=0"
    input := "dsolve(yp + y = 0)"
    check := fun e => isEqY e && dependsOn e "C" },
  { name := "dsolve yp+y=x"
    input := "dsolve(yp + y = x)"
    check := fun e => isEqY e && dependsOn e "x" && dependsOn e "C" },
  { name := "dsolve yp= x*y separable"
    input := "dsolve(yp = x*y)"
    check := fun e =>
      match asEquation? e with
      | some _ => true
      | none => false },
  { name := "Bernoulli yp = y²"
    input := "dsolve(yp = y^2)"
    check := fun e =>
      isEqY e && dependsOn e "C" && dependsOn e "x" },
  { name := "Bernoulli yp + y/x = y²"
    input := "dsolve(yp + y/x = y^2)"
    check := fun e => isEqY e && dependsOn e "C" },
  { name := "Bernoulli IC y(0)=1"
    input := "dsolve(yp = y^2, 0, 1)"
    check := fun e =>
      match asEquation? e with
      | some (_, r) =>
          !dependsOn r "C"
            && equivNF (simplify (subst r "x" (0 : Expr))) (1 : Expr)
      | none => false },
  { name := "homogeneous (x+y)/(x-y)"
    input := "dsolve(yp = (x+y)/(x-y))"
    check := fun e => dependsOn e "C" && dependsOn e "y" && dependsOn e "x" },
  { name := "homogeneous (x²+y²)/(x y)"
    input := "dsolve(yp = (x^2+y^2)/(x*y))"
    check := fun e => dependsOn e "C" && dependsOn e "y" },
  { name := "dsolve yp-2*y=0"
    input := "dsolve(yp - 2*y = 0)"
    check := fun e => isEqY e && dependsOn e "C" },
  { name := "dsolve with explicit y,x"
    input := "dsolve(yp + y = 0, y, x)"
    check := fun e => isEqY e },
  -- Property: closed form for sum k matches known poly after subst n↦5
  { name := "sum k at n=5 equals 15"
    input := "subst(sum(k, 1, n, k), n, 5)"
    check := fun e => simplify e == ofInt 15 },
  { name := "sum k² at n=3 equals 14"
    input := "subst(sum(k^2, k, 1, n), n, 3)"
    check := fun e => simplify e == ofInt 14 },
  { name := "numeric sum k=1..10"
    input := "sum(k, 1, 10, k)"
    check := fun e => simplify e == ofInt 55 },
  { name := "numeric sum k²=1..5"
    input := "sum(k^2, k, 1, 5)"
    check := fun e => simplify e == ofInt 55 },
  { name := "sum k^7 Faulhaber numeric"
    input := "sum(k^7, k, 1, 10)"
    check := fun e => simplify e == ofInt 18080425 },
  { name := "sum k^10 Faulhaber numeric"
    input := "sum(k^10, k, 1, 5)"
    check := fun e => simplify e == ofInt 10874275 },
  { name := "Gosper 1/(k(k+1))"
    input := "sum(1/(k*(k+1)), k, 1, n)"
    check := fun e => equivNF e (div (var "n") (add (var "n") one)) },
  { name := "Gosper k·2^k numeric"
    input := "sum(k*2^k, k, 1, 5)"
    check := fun e => simplify e == ofInt 258 },
  { name := "Gosper k·2^k closed"
    input := "sum(k*2^k, k, 1, n)"
    check := fun e =>
      equivNF (simplify (subst e "n" (ofInt 3))) (ofInt 34)
        && dependsOn e "n" },
  { name := "y' syntax dsolve"
    input := "dsolve(y' + y = 0)"
    check := fun e => isEqY e && dependsOn e "C" },
  { name := "IC y(0)=1"
    input := "dsolve(yp + y = 0, 0, 1)"
    check := fun e =>
      match asEquation? e with
      | some (l, r) =>
          l == var "y" && !dependsOn r "C"
            && equivNF (simplify (subst r "x" (0 : Expr))) (1 : Expr)
      | none => false },
  { name := "IC y(0)=2 full args"
    input := "dsolve(yp + y = 0, y, x, 0, 2)"
    check := fun e =>
      match asEquation? e with
      | some (_, r) =>
          equivNF (simplify (subst r "x" (0 : Expr))) (2 : Expr)
      | none => false },
  { name := "tidy exp form C·exp(-x)"
    input := "dsolve(yp + y = 0)"
    check := fun e =>
      let s := Expr.toString e
      s.contains "exp(-" },
  -- PR O: second-order const-coeff + linear systems
  { name := "y'' + y = 0 harmonic"
    input := "dsolve(y'' + y = 0)"
    check := fun e =>
      isEqY e && dependsOn e "C1" && dependsOn e "C2"
        && (Expr.toString e).contains "sin"
        && (Expr.toString e).contains "cos" },
  { name := "ypp alias for y''"
    input := "dsolve(ypp - y = 0)"
    check := fun e =>
      isEqY e && (Expr.toString e).contains "exp" },
  { name := "repeated root (D−1)²y=0"
    input := "dsolve(y'' + 2*yp + y = 0)"
    check := fun e =>
      isEqY e && dependsOn e "x"
        && (Expr.toString e).contains "exp" },
  { name := "distinct real roots"
    input := "dsolve(y'' - 3*yp + 2*y = 0)"
    check := fun e =>
      isEqY e && dependsOn e "C1" && dependsOn e "C2" },
  { name := "nonhomogeneous y''+y=sin(x)"
    input := "dsolve(y'' + y = sin(x))"
    check := fun e =>
      match asEquation? e with
      | some (_, r) =>
          dependsOn r "C1" && dependsOn r "C2"
            &&
            let yp := simplify (Expr.subst (Expr.subst r "C1" (0:Expr)) "C2" (0:Expr))
            let want := simplify (neg (mul (mul (ofRat ⟨1, 2⟩) (var "x")) (cos (var "x"))))
            yp == want || equivNF yp want
      | none => false },
  { name := "nonhomogeneous y''+y=1"
    input := "dsolve(y'' + y = 1)"
    check := fun e =>
      match asEquation? e with
      | some (_, r) =>
          dependsOn r "C1"
            && equivNF
                (simplify (subst (subst (subst r "C1" (0:Expr)) "C2" (0:Expr)) "x" (0:Expr)))
                (1:Expr)
      | none => false },
  { name := "2nd-order IC y(0)=1, y'(0)=0"
    input := "dsolve(y'' + y = 0, 0, 1, 0)"
    check := fun e =>
      match asEquation? e with
      | some (_, r) =>
          !dependsOn r "C1" && !dependsOn r "C2"
            && equivNF (simplify (subst r "x" (0:Expr))) (1:Expr)
      | none => false },
  { name := "linear system diagonal"
    input := "dsolve([1, 0; 0, 2])"
    check := fun e =>
      match asNamedSolution? e with
      | some pairs =>
          pairs.length == 2
            && pairs.any (fun p => p.1 == "y1" && dependsOn p.2 "C1")
            && pairs.any (fun p => p.1 == "y2" && dependsOn p.2 "C2")
      | none =>
          (prettySolution e).contains "y1" && (prettySolution e).contains "exp" },
  { name := "linear system with IC"
    input := "dsolve([1, 0; 0, 2], [3; 4])"
    check := fun e =>
      let s := prettySolution e
      s.contains "y1" && s.contains "y2" && !s.contains "C1" },
  { name := "dsolve defective nilpotent"
    input := "dsolve([0, 1; 0, 0])"
    check := fun e =>
      let s := prettySolution e
      s.contains "y1" && s.contains "y2" && s.contains "x"
        && (s.contains "C1" || s.contains "C2" || s.contains "C") },
  { name := "dsolve defective IC"
    input := "dsolve([0, 1; 0, 0], [1; 0])"
    check := fun e =>
      match asNamedSolution? e with
      | some pairs =>
          !pairs.any (fun p => dependsOn p.2 "C1" || dependsOn p.2 "C2")
            && pairs.any (fun p => p.1 == "y1")
            && pairs.any (fun p => p.1 == "y2")
      | none =>
          let s := prettySolution e
          s.contains "y1" && !s.contains "C1" }
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
  String.intercalate "\n" (s!"Sum/ODE regression: {n}/{total} passed" :: lines)

def runSuiteIO : IO UInt32 := do
  let results := runSuite
  IO.println (formatReport results)
  if allPassed results then
    IO.println "All sum/ODE regression cases passed."
    pure 0
  else
    IO.println "Sum/ODE regression failures detected."
    pure 1

#guard allPassed (runSuite suite)
#guard suite.length ≥ 18

end Taschenrechner.SumODERegression
