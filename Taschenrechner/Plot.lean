/-
  Plot expressions with gnuplot.

  * `plot` / `plot()` / `gnuplot` — gnuplot command-line shell
  * `plot(f)`              — plot f, then drop into the gnuplot CLI
  * `plot(f, a, b)`        — optional sample window [a,b] if data fallback
  * `plot(f, x, a, b)`     — free variable `x`
  * `plot(f, a, b, n)`     — n samples / gnuplot `set samples`
  * `plotpng(f[, …])`      — write PNG instead of an interactive session

  On a TTY, interactive `plot` starts gnuplot and **feeds commands on
  stdin**, then runs a `gnuplot>` prompt that forwards lines to that
  process. Type gnuplot commands (`set xrange [-5:5]`, `replot`,
  `help`, …); `quit` / `exit` returns to the CAS.

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

/-- How to drive gnuplot after writing the script. -/
inductive PlotMode where
  /-- Write PNG and wait. -/
  | png
  /-- Hand the TTY to gnuplot's interactive CLI. -/
  | shell
  /-- No TTY: detach, persist the window, pause until it is closed. -/
  | detach
  deriving Repr, BEq, Inhabited

/-- Plot specification. -/
structure PlotSpec where
  expr    : Expr
  var     : String := "x"
  lo      : Float := -10
  hi      : Float := 10
  nPoints : Nat := 400
  /-- If set, write a PNG instead of an interactive session. -/
  pngPath : Option String := none
  /-- Bare gnuplot CLI with no curve preloaded. -/
  shellOnly : Bool := false
  deriving Repr, Inhabited

/-- Marker prefix for plot-spec matrices. -/
def plotMarker : String := "__plot__"

/-- Marker for a bare gnuplot CLI session (`plot()` / `plot`). -/
def plotShellMarker : String := "__plot_shell__"

/-- Encode a plot request as an expression (for the parser → CLI path). -/
def plotSpecToExpr (s : PlotSpec) : Expr :=
  if s.shellOnly then
    Expr.mat #[#[var plotShellMarker]]
  else
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
    if rows.size == 1 && rows[0]!.size == 1 then
      match rows[0]![0]! with
      | var m =>
        if m == plotShellMarker then
          some { expr := var "x", shellOnly := true }
        else none
      | _ => none
    else if rows.size == 1 && rows[0]!.size == 7 then
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
    else if Expr.isPiName name then some "pi"
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
  | asin a => match go a with | some s => some s!"asin({s})" | none => none
  | acos a => match go a with | some s => some s!"acos({s})" | none => none
  | sec a => match go a with | some s => some s!"1/cos({s})" | none => none
  | csc a => match go a with | some s => some s!"1/sin({s})" | none => none
  | cot a => match go a with | some s => some s!"cos({s})/sin({s})" | none => none
  | factorial a => match go a with | some s => some s!"gamma(({s})+1)" | none => none
  | gamma a => match go a with | some s => some s!"gamma({s})" | none => none
  | floor a => match go a with | some s => some s!"floor({s})" | none => none
  | Expr.ite c t e =>
    match go c, go t, go e with
    | some sc, some st, some se => some s!"(({sc}) ? ({st}) : ({se}))"
    | _, _, _ => none
  | abs a => match go a with | some s => some s!"abs({s})" | none => none
  | re a => go a  -- real-valued path only
  | im a =>
    match go a with
    | some _ => some "0"  -- real embedding
    | none => none
  | conj a => go a
  | eq a b =>
    match go a, go b with
    | some sa, some sb => some s!"(({sa}) == ({sb}))"
    | _, _ => none
  | lt a b =>
    match go a, go b with
    | some sa, some sb => some s!"(({sa}) < ({sb}))"
    | _, _ => none
  | le a b =>
    match go a, go b with
    | some sa, some sb => some s!"(({sa}) <= ({sb}))"
    | _, _ => none
  | mat _ => none

/-- Shared terminal / axes setup for gnuplot scripts. -/
def gnuplotPreamble (s : PlotSpec) (title : String) (mode : PlotMode) : String :=
  let title := gnuplotEscape title
  let header :=
    match mode with
    | .shell =>
        "# Taschenrechner — gnuplot CLI (help; quit returns to the CAS)\n"
    | _ => ""
  let term :=
    match mode with
    | .png =>
      match s.pngPath with
      | some path =>
          s!"set terminal pngcairo size 900,600 enhanced font 'sans,12'\nset output \"{gnuplotEscape path}\"\n"
      | none =>
          "set terminal pngcairo size 900,600 enhanced font 'sans,12'\nset output \"plot.png\"\n"
    | .shell =>
        -- persist: stdin is a pipe (not a tty), so the qt window must not
        -- depend on gnuplot thinking it is an interactive session
        "set mouse\nset terminal qt size 900,600 enhanced font 'sans,12' persist\n"
    | .detach =>
        "set mouse\nset terminal qt size 900,600 enhanced font 'sans,12' persist\n"
  header ++ term ++
    "set grid\n" ++
    s!"set xlabel '{s.var}'\n" ++
    "set ylabel 'y'\n" ++
    s!"set title \"{title}\"\n" ++
    "set zeroaxis lt -1\n" ++
    -- Use the CAS free variable as gnuplot's dummy independent variable
    s!"set dummy {s.var}\n" ++
    s!"set samples {s.nPoints}\n"

def gnuplotEpilogue (mode : PlotMode) : String :=
  match mode with
  | .png => "set output\n"
  | .shell => ""  -- remain at the gnuplot> prompt
  | .detach => "pause mouse close\n"

/-- Native formula plot: let gnuplot choose the default xrange (no `[lo:hi]`). -/
def formatGnuplotScriptNative (s : PlotSpec) (formula : String) (mode : PlotMode) : String :=
  let title := shortTitle (Expr.toString s.expr)
  gnuplotPreamble s title mode ++
    s!"plot {formula} with lines lw 2 title \"{gnuplotEscape title}\"\n" ++
    gnuplotEpilogue mode

/-- Data-file plot (sampled in Lean); autoscale axes from the data. -/
def formatGnuplotScriptData (s : PlotSpec) (dataPath : String) (mode : PlotMode) : String :=
  let title := shortTitle (Expr.toString s.expr)
  gnuplotPreamble s title mode ++
    s!"plot '{gnuplotEscape dataPath}' using 1:2 with lines lw 2 title \"{gnuplotEscape title}\"\n" ++
    gnuplotEpilogue mode

/-- Count successfully sampled points. -/
def countValid (pts : Array (Float × Option Float)) : Nat :=
  pts.foldl (fun n p => match p.2 with | some _ => n + 1 | none => n) 0

/-- True when stdin is a terminal (so we can hand it to gnuplot). -/
def stdinIsTty : IO Bool := do
  (← IO.getStdin).isTty

/-- Pick a driver from the spec and whether we have a TTY. -/
def choosePlotMode (s : PlotSpec) : IO PlotMode := do
  if s.pngPath.isSome then
    return .png
  else if (← stdinIsTty) then
    return .shell
  else
    return .detach

def gnuplotMissingError : String :=
  "plot: gnuplot not found in PATH (install gnuplot)"

/-- Check that `gnuplot` is on PATH. -/
def ensureGnuplot : IO (Except String Unit) := do
  let which ← IO.Process.output { cmd := "which", args := #["gnuplot"] }
  if which.exitCode != 0 then
    return .error gnuplotMissingError
  return .ok ()

/-- Ensure a command block ends with a newline so gnuplot executes it. -/
def gnuplotEnsureNl (s : String) : String :=
  if s.isEmpty || s.endsWith "\n" then s else s ++ "\n"

def isGnuplotQuit (line : String) : Bool :=
  let t := line.trimAscii.toString.toLower
  t == "quit" || t == "exit" || t == "q" || t == ":q"

/--
  Forward user lines to a live gnuplot process (stdin is a pipe).
  `quit` / `exit` / EOF close gnuplot and return to the CAS.
-/
partial def gnuplotStdinLoop (h : IO.FS.Handle)
    (child : IO.Process.Child { stdin := .null }) : IO (Except String Unit) := do
  match ← child.tryWait with
  | some code =>
    if code != 0 then
      return .error s!"plot: gnuplot exited {code}"
    return .ok ()
  | none =>
    IO.print "gnuplot> "
    (← IO.getStdout).flush
    let raw ← (← IO.getStdin).getLine
    if raw.isEmpty then
      try
        h.putStr "exit\n"
        h.flush
      catch _ => pure ()
      let _ ← child.wait
      return .ok ()
    let line := raw.trimAscii.toString
    if line.isEmpty then
      gnuplotStdinLoop h child
    else if isGnuplotQuit line then
      try
        h.putStr "exit\n"
        h.flush
      catch _ => pure ()
      let _ ← child.wait
      return .ok ()
    else
      try
        h.putStr (line ++ "\n")
        h.flush
      catch _ =>
        let code ← child.wait
        if code != 0 then
          return .error s!"plot: gnuplot exited {code}"
        return .ok ()
      gnuplotStdinLoop h child

/-- Banner printed before the stdin-fed gnuplot prompt. -/
def gnuplotShellBanner : String :=
  "(gnuplot CLI — type gnuplot commands; help; quit returns)"

/--
  Start gnuplot with piped stdin, write `commands`, then run `gnuplot>`.
  No script file is passed on gnuplot's command line.
-/
def invokeGnuplotShell (commands : String) : IO (Except String Unit) := do
  if !(← stdinIsTty) then
    return .error "gnuplot: interactive CLI requires a terminal (use plotpng for batch)"
  let child ← IO.Process.spawn {
    cmd := "gnuplot"
    stdin := .piped
    stdout := .inherit
    stderr := .inherit
  }
  let cmds := gnuplotEnsureNl commands
  if !cmds.isEmpty then
    child.stdin.putStr cmds
    child.stdin.flush
  let (h, child) ← child.takeStdin
  IO.println gnuplotShellBanner
  (← IO.getStdout).flush
  gnuplotStdinLoop h child

/--
  Feed gnuplot via stdin (never a script-file argument).

  * `png`    — write commands on stdin, wait for completion
  * `shell`  — write commands, then an interactive `gnuplot>` loop
  * `detach` — write commands (persist + pause) and return
-/
def invokeGnuplot (commands : String) (mode : PlotMode) : IO (Except String Unit) := do
  match mode with
  | .png =>
    let r ← IO.Process.output { cmd := "gnuplot" } (some (gnuplotEnsureNl commands))
    if r.exitCode != 0 then
      let err := r.stderr.trimAscii.toString
      return .error s!"plot: gnuplot failed (exit {r.exitCode}){if err.isEmpty then "" else s!": {err}"}"
    return .ok ()
  | .shell =>
    invokeGnuplotShell commands
  | .detach =>
    let child ← IO.Process.spawn {
      cmd := "gnuplot"
      stdin := .piped
      stdout := .null
      stderr := .null
      setsid := true
    }
    child.stdin.putStr (gnuplotEnsureNl commands)
    child.stdin.flush
    let _ ← child.takeStdin
    return .ok ()

/-- Enter a bare gnuplot command-line session (no curve preloaded). -/
def runBareGnuplotShell : IO (Except String String) := do
  match ← ensureGnuplot with
  | .error err => return .error err
  | .ok () => pure ()
  match ← invokeGnuplotShell "" with
  | .error err => return .error err
  | .ok () => return .ok "(left gnuplot)"

/-- Status line for a finished / detached plot. -/
def plotResultMessage (s : PlotSpec) (mode : PlotMode) (detail : String) : String :=
  match mode with
  | .png =>
    match s.pngPath with
    | some p => s!"{detail} → {p}"
    | none => detail
  | .shell => s!"{detail}\n{gnuplotShellBanner}"
  | .detach => s!"{detail}\n(gnuplot left running)"

/--
  Run gnuplot for the given spec.
  Uses a **native gnuplot formula** when possible; otherwise samples in Lean.
  On a TTY, interactive plots hand the terminal to the gnuplot CLI.
-/
def runPlot (s : PlotSpec) : IO (Except String String) := do
  match ← ensureGnuplot with
  | .error err => return .error err
  | .ok () => pure ()
  if s.shellOnly then
    return (← runBareGnuplotShell)
  let mode ← choosePlotMode s
  let tmp ← IO.FS.createTempDir
  let finish (commands msg : String) : IO (Except String String) := do
    match mode with
    | .shell =>
      IO.println msg
      (← IO.getStdout).flush
      match ← invokeGnuplot commands mode with
      | .error err => return .error err
      | .ok () => return .ok "(left gnuplot)"
    | _ =>
      match ← invokeGnuplot commands mode with
      | .error err => return .error err
      | .ok () => return .ok msg
  match toGnuplotFormula? s.expr s.var with
  | some formula =>
    let commands := formatGnuplotScriptNative s formula mode
    -- PNG: if the formula is rejected, fall back to sampled data.
    -- Shell: errors show on gnuplot's stderr; the prompt stays up.
    if mode == .png then
      match ← invokeGnuplot commands mode with
      | .error err =>
        let pts := sampleCurve s.expr s.var s.lo s.hi s.nPoints
        let nOk := countValid pts
        if nOk == 0 then return .error err
        let dataPath := tmp / "data.dat"
        IO.FS.writeFile dataPath (formatPlotData pts)
        let commands := formatGnuplotScriptData s (toString dataPath) mode
        match ← invokeGnuplot commands mode with
        | .error err2 => return .error err2
        | .ok () =>
          return .ok (plotResultMessage s mode s!"plotted {nOk} samples (data fallback)")
      | .ok () =>
        return .ok (plotResultMessage s mode s!"plotted via gnuplot formula\n  {formula}")
    else
      finish commands (plotResultMessage s mode s!"plotted via gnuplot formula\n  {s.var} ↦ {formula}")
  | none =>
    let pts := sampleCurve s.expr s.var s.lo s.hi s.nPoints
    let nOk := countValid pts
    if nOk == 0 then
      return .error "plot: no finite real sample points (and expression is not a native gnuplot formula)"
    let dataPath := tmp / "data.dat"
    IO.FS.writeFile dataPath (formatPlotData pts)
    let commands := formatGnuplotScriptData s (toString dataPath) mode
    let detail := s!"plotted {nOk} samples"
    match mode with
    | .png =>
      match ← invokeGnuplot commands mode with
      | .error err => return .error err
      | .ok () => return .ok (plotResultMessage s mode detail)
    | _ =>
      finish commands (plotResultMessage s mode detail)

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
  | [] =>
    pure { expr := var "x", shellOnly := true }
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
    throw "plot: plot | plot() | plot(f) | plot(f,a,b) | plot(f,x,a,b) | plot(f,a,b,n) | plot(f,x,a,b,n) [| png path]"

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
