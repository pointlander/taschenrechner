/-
  Plot expressions with gnuplot.

  * `plot(f)`              — f(x) on [-10, 10]
  * `plot(f, a, b)`        — range [a, b]
  * `plot(f, x, a, b)`     — free variable `x`
  * `plot(f, a, b, n)`     — n sample points
  * `plot(f, x, a, b, n)`
  * Optional PNG: `plot(f, a, b, "out.png")` via string is not supported;
    use `plotpng(f, path, a, b)` instead.

  Builds a temp data file + gnuplot script and runs `gnuplot -persist`.
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

/-- Escape a string for double-quoted gnuplot titles. -/
def gnuplotEscape (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- Truncate title for gnuplot. -/
def shortTitle (t : String) : String :=
  if t.length ≤ 60 then t
  else String.ofList (t.toList.take 57) ++ "..."

/-- Build gnuplot script that reads `dataPath`. -/
def formatGnuplotScript (s : PlotSpec) (dataPath : String) : String :=
  let title := gnuplotEscape (shortTitle (Expr.toString s.expr))
  let term :=
    match s.pngPath with
    | some path =>
        s!"set terminal pngcairo size 900,600 enhanced font 'sans,12'\nset output \"{gnuplotEscape path}\"\n"
    | none =>
        "set terminal qt size 900,600 enhanced font 'sans,12' persist\n"
  term ++
    "set grid\n" ++
    "set xlabel '" ++ s.var ++ "'\n" ++
    "set ylabel 'y'\n" ++
    s!"set title \"{title}\"\n" ++
    "set zeroaxis lt -1\n" ++
    s!"plot '{gnuplotEscape dataPath}' using 1:2 with lines lw 2 title \"{title}\"\n" ++
    (match s.pngPath with
     | some _ => "set output\n"
     | none => "")

/-- Count successfully sampled points. -/
def countValid (pts : Array (Float × Option Float)) : Nat :=
  pts.foldl (fun n p => match p.2 with | some _ => n + 1 | none => n) 0

/--
  Run gnuplot for the given spec.
  Returns a human-readable status message or an error.
-/
def runPlot (s : PlotSpec) : IO (Except String String) := do
  -- Ensure gnuplot exists
  let which ← IO.Process.output { cmd := "which", args := #["gnuplot"] }
  if which.exitCode != 0 then
    return .error "plot: gnuplot not found in PATH (install gnuplot)"
  let pts := sampleCurve s.expr s.var s.lo s.hi s.nPoints
  let nOk := countValid pts
  if nOk == 0 then
    return .error "plot: no finite real sample points (check domain / free variables)"
  let tmp ← IO.FS.createTempDir
  let dataPath := tmp / "data.dat"
  let scriptPath := tmp / "plot.gp"
  IO.FS.writeFile dataPath (formatPlotData pts)
  IO.FS.writeFile scriptPath (formatGnuplotScript s (toString dataPath))
  let r ← IO.Process.output {
    cmd := "gnuplot"
    args :=
      match s.pngPath with
      | some _ => #[toString scriptPath]
      | none => #["-persist", toString scriptPath]
  }
  if r.exitCode != 0 then
    let err := r.stderr.trimAscii.toString
    return .error s!"plot: gnuplot failed (exit {r.exitCode}){if err.isEmpty then "" else s!": {err}"}"
  let msg :=
    match s.pngPath with
    | some p => s!"plotted {nOk} points → {p}"
    | none => s!"plotted {nOk} points on [{s.lo}, {s.hi}] (gnuplot window)"
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
