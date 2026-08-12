/-
  Plot expressions with gnuplot.

  * `plot(f)`              — f vs free var (default x); no xrange forced
  * `plot(f, a, b)`        — optional sample window [a,b] if data fallback
  * `plot(f, x, a, b)`     — free variable `x`
  * `plot(f, a, b, n)`     — n samples / gnuplot `set samples`
  * `plotpng(f[, …])`      — write PNG instead of interactive window

  Prefer **native gnuplot formulas** (`plot sin(x)`) with gnuplot's default
  axis scaling. Do **not** emit `plot [lo:hi] …`. Data fallback still samples
  on [lo,hi] (default [-10,10]) only when a formula cannot be emitted.
-/
import Taschenrechner.Expr
import Taschenrechner.Simplify
import Taschenrechner.Eval
import Taschenrechner.Numeric
import Taschenrechner.Matrix

namespace Taschenrechner

open Expr

/-- Plot specification. -/
structure PlotSpec where
  expr    : Expr
  var     : String := "x"
  lo      : Float := -10
  hi      : Float := 10
  nPoints : Nat := 400
  /-- If set, write a PNG instead of an interactive window. -/
  pngPath : Option String := none
  deriving Repr, Inhabited

/-- Marker prefix for plot-spec matrices. -/
def plotMarker : String := "__plot__"

/-- Encode a plot request as an expression (for the parser → CLI path). -/
def plotSpecToExpr (s : PlotSpec) : Expr :=
  let loE := ofRat (floatToRat s.lo 8)
  let hiE := ofRat (floatToRat s.hi 8)
  let nE := ofNat s.nPoints
  let pngE :=
    match s.pngPath with
    | none => var ""
    | some p => var p
  Expr.mat #[#[var plotMarker, s.expr, var s.var, loE, hiE, nE, pngE]]

/-- Decode a plot request; `none` if not a plot marker. -/
def asPlotSpec? (e : Expr) : Option PlotSpec :=
  match e with
  | mat rows =>
    if rows.size == 1 && rows[0]!.size == 7 then
      let row := rows[0]!
      match row[0]! with
      | var m =>
        if m != plotMarker then none
        else
          let body := row[1]!
          let v :=
            match row[2]! with
            | var name => name
            | _ => "x"
          let lo :=
            match evalFloats? row[3]! with
            | some (r, _) => r
            | none => -10
          let hi :=
            match evalFloats? row[4]! with
            | some (r, _) => r
            | none => 10
          let n :=
            match row[5]! with
            | const c =>
              match CplxConst.toRat? c with
              | some q =>
                if q.den == 1 && q.num > 0 then q.num.toNat else 400
              | none => 400
            | _ => 400
          let png :=
            match row[6]! with
            | var p => if p.isEmpty then none else some p
            | _ => none
          some {
            expr := body
            var := v
            lo := lo
            hi := if hi ≤ lo then lo + 1 else hi
            nPoints := min (max n 2) 10000
            pngPath := png
          }
      | _ => none
    else none
  | _ => none

/-- Evaluate expression at a real float for variable `v` (real part). -/
def evalAtFloat (e : Expr) (v : String) (x : Float) : Option Float :=
  let xe := ofRat (floatToRat x 10)
  let e' := simplify (Expr.subst e v xe)
  match evalFloatsWithSqrt? e' with
  | some (r, i) =>
    if i != 0 && Float.abs i > 1e-9 then none  -- non-real
    else if r.isNaN || r.isInf then none
    else some r
  | none => none

/-- Sample `n` points on [lo, hi]. Gaps (none) become blank lines for gnuplot. -/
def sampleCurve (e : Expr) (v : String) (lo hi : Float) (n : Nat) :
    Array (Float × Option Float) :=
  let n := max n 2
  let span := hi - lo
  Id.run do
    let mut pts : Array (Float × Option Float) := Array.empty
    for i in [:n] do
      let t := i.toFloat / (n - 1).toFloat
      let x := lo + span * t
      pts := pts.push (x, evalAtFloat e v x)
    pure pts

/-- Format points as gnuplot data (blank line on missing values breaks the line). -/
def formatPlotData (pts : Array (Float × Option Float)) : String :=
  Id.run do
    let mut lines : List String := []
    for p in pts do
      let x := p.1
      match p.2 with
      | none => lines := lines ++ [""]
      | some y => lines := lines ++ [s!"{x} {y}"]
    pure (String.intercalate "\n" lines ++ "\n")

/-- Escape a string for double-quoted gnuplot titles / paths. -/
def gnuplotEscape (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- Truncate title for gnuplot. -/
def shortTitle (t : String) : String :=
  if t.length ≤ 60 then t
  else String.ofList (t.toList.take 57) ++ "..."

/-- Parenthesize a gnuplot subexpression when needed. -/
def gpParen (s : String) : String := s!"({s})"

/--
  Translate `e` to a gnuplot formula in free variable `v`.
  Returns `none` if the expression uses features gnuplot cannot evaluate
  (matrices, relations, free symbols other than `v`, complex non-reals, …).
-/
partial def toGnuplotFormula? (e : Expr) (v : String) : Option String :=
  go (simplify e)
where
  go : Expr → Option String
  | const c =>
    match CplxConst.toRat? c with
    | some q =>
      if q.den == 1 then some s!"{q.num}"
      else some s!"({q.num}.0/{q.den}.0)"
    | none => none  -- pure imaginary / complex
  | var name =>
    if name == v then some name
    else if isInfName name then none
    else none  -- other free symbols not supported natively
  | add a b =>
    match go a, go b with
    | some sa, some sb => some s!"({sa})+({sb})"
    | _, _ => none
  | mul a b =>
    -- Detect a * b^(-1) → a/b
    match a, b with
    | _, pow d (const r) =>
      match CplxConst.toRat? r, go a, go d with
      | some q, some sa, some sd =>
        if q == RatConst.negOne then some s!"({sa})/({sd})"
        else
          match go b with
          | some sb => some s!"({sa})*({sb})"
          | none => none
      | _, _, _ =>
        match go a, go b with
        | some sa, some sb => some s!"({sa})*({sb})"
        | _, _ => none
    | pow d (const r), _ =>
      match CplxConst.toRat? r, go b, go d with
      | some q, some sb, some sd =>
        if q == RatConst.negOne then some s!"({sb})/({sd})"
        else
          match go a with
          | some sa => some s!"({sa})*({sb})"
          | none => none
      | _, _, _ =>
        match go a, go b with
        | some sa, some sb => some s!"({sa})*({sb})"
        | _, _ => none
    | _, _ =>
      match go a, go b with
      | some sa, some sb => some s!"({sa})*({sb})"
      | _, _ => none
  | pow a b =>
    match b with
    | const r =>
      match CplxConst.toRat? r with
      | some q =>
        if q == ⟨1, 2⟩ then
          match go a with
          | some sa => some s!"sqrt({sa})"
          | none => none
        else if q == RatConst.negOne then
          match go a with
          | some sa => some s!"(1.0)/({sa})"
          | none => none
        else
          match go a with
          | some sa =>
            if q.den == 1 then some s!"({sa})**({q.num})"
            else some s!"({sa})**({q.num}.0/{q.den}.0)"
          | none => none
      | none => none
    | _ =>
      match go a, go b with
      | some sa, some sb => some s!"({sa})**({sb})"
      | _, _ => none
  | sin a => match go a with | some s => some s!"sin({s})" | none => none
  | cos a => match go a with | some s => some s!"cos({s})" | none => none
  | tan a => match go a with | some s => some s!"tan({s})" | none => none
  | sinh a => match go a with | some s => some s!"sinh({s})" | none => none
  | cosh a => match go a with | some s => some s!"cosh({s})" | none => none
  | tanh a => match go a with | some s => some s!"tanh({s})" | none => none
  | exp a => match go a with | some s => some s!"exp({s})" | none => none
  | ln a => match go a with | some s => some s!"log({s})" | none => none  -- gnuplot log = ln
  | atan a => match go a with | some s => some s!"atan({s})" | none => none
  | abs a => match go a with | some s => some s!"abs({s})" | none => none
  | re a => go a  -- real-valued path only
  | im a =>
    match go a with
    | some _ => some "0"  -- real embedding
    | none => none
  | conj a => go a
  | eq _ _ | lt _ _ | le _ _ | mat _ => none

/-- Shared terminal / axes setup for gnuplot scripts. -/
def gnuplotPreamble (s : PlotSpec) (title : String) : String :=
  let title := gnuplotEscape title
  let term :=
    match s.pngPath with
    | some path =>
        s!"set terminal pngcairo size 900,600 enhanced font 'sans,12'\nset output \"{gnuplotEscape path}\"\n"
    | none =>
        "set mouse\nset terminal qt size 900,600 enhanced font 'sans,12' persist\n"
  term ++
    "set grid\n" ++
    s!"set xlabel '{s.var}'\n" ++
    "set ylabel 'y'\n" ++
    s!"set title \"{title}\"\n" ++
    "set zeroaxis lt -1\n" ++
    -- Use the CAS free variable as gnuplot's dummy independent variable
    s!"set dummy {s.var}\n" ++
    s!"set samples {s.nPoints}\n"

def gnuplotEpilogue (s : PlotSpec) : String :=
  match s.pngPath with
  | some _ => "set output\n"
  | none => "pause mouse close\n"

/-- Native formula plot: let gnuplot choose the default xrange (no `[lo:hi]`). -/
def formatGnuplotScriptNative (s : PlotSpec) (formula : String) : String :=
  let title := shortTitle (Expr.toString s.expr)
  gnuplotPreamble s title ++
    s!"plot {formula} with lines lw 2 title \"{gnuplotEscape title}\"\n" ++
    gnuplotEpilogue s

/-- Data-file plot (sampled in Lean); autoscale axes from the data. -/
def formatGnuplotScriptData (s : PlotSpec) (dataPath : String) : String :=
  let title := shortTitle (Expr.toString s.expr)
  gnuplotPreamble s title ++
    s!"plot '{gnuplotEscape dataPath}' using 1:2 with lines lw 2 title \"{gnuplotEscape title}\"\n" ++
    gnuplotEpilogue s

/-- Count successfully sampled points. -/
def countValid (pts : Array (Float × Option Float)) : Nat :=
  pts.foldl (fun n p => match p.2 with | some _ => n + 1 | none => n) 0

/--
  Invoke gnuplot on a script file.

  * `wait := true`  — run to completion (PNG / batch)
  * `wait := false` — spawn and return immediately; do not wait or kill the child
    (`setsid` detaches so the plot survives when the CAS process exits)
-/
def invokeGnuplot (scriptPath : String) (wait : Bool) : IO (Except String Unit) := do
  if wait then
    let r ← IO.Process.output {
      cmd := "gnuplot"
      args := #[scriptPath]
    }
    if r.exitCode != 0 then
      let err := r.stderr.trimAscii.toString
      return .error s!"plot: gnuplot failed (exit {r.exitCode}){if err.isEmpty then "" else s!": {err}"}"
    return .ok ()
  else
    -- Leave the process running (pause mouse close keeps the window open).
    let _ ← IO.Process.spawn {
      cmd := "gnuplot"
      args := #[scriptPath]
      stdin := .null
      stdout := .null
      stderr := .null
      setsid := true
    }
    return .ok ()

/--
  Run gnuplot for the given spec.
  Uses a **native gnuplot formula** when possible; otherwise samples in Lean.
  Interactive windows are spawned without waiting on the gnuplot process.
-/
def runPlot (s : PlotSpec) : IO (Except String String) := do
  let which ← IO.Process.output { cmd := "which", args := #["gnuplot"] }
  if which.exitCode != 0 then
    return .error "plot: gnuplot not found in PATH (install gnuplot)"
  let waitForExit := s.pngPath.isSome
  let tmp ← IO.FS.createTempDir
  let scriptPath := tmp / "plot.gp"
  match toGnuplotFormula? s.expr s.var with
  | some formula =>
    IO.FS.writeFile scriptPath (formatGnuplotScriptNative s formula)
    match ← invokeGnuplot (toString scriptPath) waitForExit with
    | .error err =>
      -- Rare: formula parse failed in gnuplot → fall back to sampling
      let pts := sampleCurve s.expr s.var s.lo s.hi s.nPoints
      let nOk := countValid pts
      if nOk == 0 then return .error err
      let dataPath := tmp / "data.dat"
      IO.FS.writeFile dataPath (formatPlotData pts)
      IO.FS.writeFile scriptPath (formatGnuplotScriptData s (toString dataPath))
      match ← invokeGnuplot (toString scriptPath) waitForExit with
      | .error err2 => return .error err2
      | .ok () =>
        let msg :=
          match s.pngPath with
          | some p => s!"plotted {nOk} samples (data fallback) → {p}"
          | none => s!"plotted {nOk} samples (data fallback; gnuplot left running)"
        return .ok msg
    | .ok () =>
      let msg :=
        match s.pngPath with
        | some p => s!"plotted via gnuplot formula → {p}\n  {formula}"
        | none => s!"plotted via gnuplot formula (gnuplot left running)\n  {s.var} ↦ {formula}"
      return .ok msg
  | none =>
    let pts := sampleCurve s.expr s.var s.lo s.hi s.nPoints
    let nOk := countValid pts
    if nOk == 0 then
      return .error "plot: no finite real sample points (and expression is not a native gnuplot formula)"
    let dataPath := tmp / "data.dat"
    IO.FS.writeFile dataPath (formatPlotData pts)
    IO.FS.writeFile scriptPath (formatGnuplotScriptData s (toString dataPath))
    match ← invokeGnuplot (toString scriptPath) waitForExit with
    | .error err => return .error err
    | .ok () =>
      let msg :=
        match s.pngPath with
        | some p => s!"plotted {nOk} samples → {p}"
        | none => s!"plotted {nOk} samples (gnuplot left running)"
      return .ok msg

/-- Build a plot spec from parser arguments (expressions). -/
def buildPlotSpec (args : List Expr) : Except String PlotSpec := do
  let asFloat (e : Expr) (label : String) : Except String Float := do
    match evalFloats? (simplify e) with
    | some (r, i) =>
      if Float.abs i > 1e-12 then throw s!"plot: {label} must be real"
      else if r.isNaN || r.isInf then throw s!"plot: {label} is not finite"
      else pure r
    | none => throw s!"plot: cannot evaluate {label} numerically"
  let asNat (e : Expr) : Except String Nat := do
    match simplify e with
    | const c =>
      match CplxConst.toRat? c with
      | some q =>
        if q.den == 1 && q.num ≥ 2 then pure q.num.toNat
        else throw "plot: point count must be an integer ≥ 2"
      | none => throw "plot: point count must be an integer ≥ 2"
    | _ => throw "plot: point count must be an integer ≥ 2"
  match args with
  | [f] =>
    pure { expr := f, var := "x", lo := -10, hi := 10, nPoints := 400 }
  | [f, a, b] =>
    -- plot(f, a, b) range on x
    match a with
    | var _ =>
      throw "plot: use plot(f, x, a, b) or plot(f, a, b)"
    | _ =>
      let lo ← asFloat a "lo"
      let hi ← asFloat b "hi"
      pure { expr := f, var := "x", lo := lo, hi := hi, nPoints := 400 }
  | [f, a, b, c] =>
    match a with
    | var v =>
      -- plot(f, x, a, b)
      let lo ← asFloat b "lo"
      let hi ← asFloat c "hi"
      pure { expr := f, var := v, lo := lo, hi := hi, nPoints := 400 }
    | _ =>
      -- plot(f, a, b, n) or plot(f, a, b, "file.png") as var path
      match c with
      | var path =>
        if path.endsWith ".png" || path.endsWith ".PNG" then
          let lo ← asFloat a "lo"
          let hi ← asFloat b "hi"
          pure { expr := f, var := "x", lo := lo, hi := hi, nPoints := 400, pngPath := some path }
        else
          let lo ← asFloat a "lo"
          let hi ← asFloat b "hi"
          let n ← asNat c
          pure { expr := f, var := "x", lo := lo, hi := hi, nPoints := n }
      | _ =>
        let lo ← asFloat a "lo"
        let hi ← asFloat b "hi"
        let n ← asNat c
        pure { expr := f, var := "x", lo := lo, hi := hi, nPoints := n }
  | [f, a, b, c, d] =>
    match a with
    | var v =>
      -- plot(f, x, a, b, n) or plot(f, x, a, b, file.png)
      match d with
      | var path =>
        if path.endsWith ".png" || path.endsWith ".PNG" then
          let lo ← asFloat b "lo"
          let hi ← asFloat c "hi"
          pure { expr := f, var := v, lo := lo, hi := hi, nPoints := 400, pngPath := some path }
        else
          let lo ← asFloat b "lo"
          let hi ← asFloat c "hi"
          let n ← asNat d
          pure { expr := f, var := v, lo := lo, hi := hi, nPoints := n }
      | _ =>
        let lo ← asFloat b "lo"
        let hi ← asFloat c "hi"
        let n ← asNat d
        pure { expr := f, var := v, lo := lo, hi := hi, nPoints := n }
    | _ => throw "plot: unexpected arguments"
  | [f, a, b, c, d, e] =>
    -- plot(f, x, a, b, n, file.png)
    let v ← match a with
      | var name => pure name
      | _ => throw "plot: expected variable name as 2nd argument"
    let lo ← asFloat b "lo"
    let hi ← asFloat c "hi"
    let n ← asNat d
    let path ← match e with
      | var p => pure p
      | _ => throw "plot: PNG path must be an identifier or quoted name (use plotpng)"
    pure { expr := f, var := v, lo := lo, hi := hi, nPoints := n, pngPath := some path }
  | _ =>
    throw "plot: plot(f) | plot(f,a,b) | plot(f,x,a,b) | plot(f,a,b,n) | plot(f,x,a,b,n) [| png path]"

/-- Convenience: plot and write PNG (default `plot.png`). -/
def buildPlotPngSpec (args : List Expr) : Except String PlotSpec := do
  match args with
  | [] => throw "plotpng: plotpng(f) | plotpng(f,a,b) | plotpng(f,name,a,b)"
  | [f] =>
    let s ← buildPlotSpec [f]
    pure { s with pngPath := some "plot.png" }
  | f :: a :: rest =>
    match a, rest with
    | var name, b :: c :: more =>
      let path := if name.endsWith ".png" then name else name ++ ".png"
      let s ← buildPlotSpec (f :: b :: c :: more)
      pure { s with pngPath := some path }
    | var name, [] =>
      let s ← buildPlotSpec [f]
      let path := if name.endsWith ".png" then name else name ++ ".png"
      pure { s with pngPath := some path }
    | _, _ =>
      let s ← buildPlotSpec (f :: a :: rest)
      pure { s with pngPath := some "plot.png" }

end Taschenrechner
