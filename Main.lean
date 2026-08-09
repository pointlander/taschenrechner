import Taschenrechner

open Taschenrechner
open Taschenrechner.Expr
open Taschenrechner.Parse

def showDiff (label : String) (e : Expr) : IO Unit := do
  let d := diff e "x"
  IO.println s!"  d/dx [{label}]  {e}"
  IO.println s!"            =  {d}"
  IO.println ""

def showInt (label : String) (e : Expr) : IO Unit := do
  IO.println s!"  ∫ [{label}]  {e}  dx"
  match integrate e "x" with
  | .success F src =>
    let check := diff F "x"
    IO.println s!"            =  {F}  + C  [{src}, verified]"
    IO.println s!"  verify d/dx =  {check}"
  | .notElementary r =>
    IO.println s!"            not elementary: {r}"
  | .failure r =>
    IO.println s!"            failed: {r}"
  IO.println ""

def runDemo : IO Unit := do
  IO.println "═══════════════════════════════════════════════"
  IO.println "  Taschenrechner — Lean 4 Computer Algebra"
  IO.println "  Symbolic differentiation & integration"
  IO.println "═══════════════════════════════════════════════"
  IO.println ""

  IO.println "── Differentiation ──────────────────────────"
  showDiff "x²"        (x ^ (2 : Expr))
  showDiff "x³ + 2x"   (x ^ (3 : Expr) + (2 : Expr) * x)
  showDiff "sin(x)"    (sin x)
  showDiff "exp(x²)"   (exp (x ^ (2 : Expr)))
  showDiff "x·ln(x)"   (x * ln x)
  showDiff "sin(x)·cos(x)" (sin x * cos x)
  showDiff "(2x+1)⁵"   (((2 : Expr) * x + 1) ^ (5 : Expr))

  IO.println "── Integration ──────────────────────────────"
  showInt "x²"         (x ^ (2 : Expr))
  showInt "3x + 1"     ((3 : Expr) * x + 1)
  showInt "1/x"        (x ^ ((-1 : Expr)))
  showInt "sin(x)"     (sin x)
  showInt "cos(2x)"    (cos ((2 : Expr) * x))
  showInt "exp(x)"     (exp x)
  showInt "exp(3x)"    (exp ((3 : Expr) * x))
  showInt "ln(x)"      (ln x)
  showInt "x·exp(x)"   (x * exp x)
  showInt "x·ln(x)"    (x * ln x)
  showInt "2x·cos(x²)" ((2 : Expr) * x * cos (x ^ (2 : Expr)))

  IO.println "── Definite integral ────────────────────────"
  let e := x ^ (2 : Expr)
  match integrateDefinite e "x" (0 : Expr) (1 : Expr) with
  | .success r src =>
    IO.println s!"  ∫₀¹ x² dx  =  {r}  [{src}]"
  | .notElementary r =>
    IO.println s!"  not elementary: {r}"
  | .failure r =>
    IO.println s!"  failed: {r}"
  IO.println ""

  IO.println "── Parser ───────────────────────────────────"
  let samples := [
    "x^2 + 3*x + 1",
    "2x(x+1)",
    "sin(x^2)",
    "diff(sin(x^2), x)",
    "int(x*exp(x))",
    "-x^2 + 1"
  ]
  for s in samples do
    match parse s with
    | .ok e => IO.println s!"  '{s}'  →  {e}"
    | .error err => IO.println s!"  '{s}'  ✗ {err}"
  IO.println ""

  IO.println "── Complex numbers ──────────────────────────"
  let cplxSamples := [
    "i^2",
    "2+3*i",
    "(1+i)*(1-i)",
    "1/i",
    "re(2+3*i)",
    "im(2+3*i)",
    "conj(2+3*i)",
    "euler(exp(i*x))"
  ]
  for s in cplxSamples do
    match parse s with
    | .ok e => IO.println s!"  '{s}'  →  {e}"
    | .error err => IO.println s!"  '{s}'  ✗ {err}"
  IO.println ""

  IO.println "── Matrices ─────────────────────────────────"
  let matSamples := [
    "[1, 2; 3, 4]",
    "det([1, 2; 3, 4])",
    "inv([1, 2; 0, 1])",
    "[1, 2; 3, 4] * eye(2)",
    "trace([1, 2; 3, 4])",
    "transpose([1, 2; 3, 4])",
    "2 * [1, 0; 0, 1]",
    "rref([1, 2; 2, 4])",
    "rank([1, 2; 2, 4])",
    "nullspace([1, 2; 2, 4])",
    "solve([1, 1; 0, 1], [3; 2])",
    "solve([1, 2; 2, 4], [3; 6])"
  ]
  for s in matSamples do
    match parse s with
    | .ok e =>
      match asMat? e with
      | some rows =>
        IO.println s!"  '{s}'  →"
        for line in (Mat.pretty rows).splitOn "\n" do
          IO.println s!"    {line}"
      | none => IO.println s!"  '{s}'  →  {e}"
    | .error err => IO.println s!"  '{s}'  ✗ {err}"
  IO.println ""

  IO.println "── Risch algorithm ──────────────────────────"
  let rischSamples := [
    "1/(x^2+1)",
    "(2*x+1)/(x^2+x+1)",
    "x^3/(x+1)",
    "exp(2*x)",
    "x*exp(x)",
    "x*exp(x^2)",
    "exp(x^2)"
  ]
  for s in rischSamples do
    match parse s with
    | .error err => IO.println s!"  '{s}'  ✗ parse: {err}"
    | .ok e =>
      match risch e "x" with
      | .elementary F =>
        IO.println s!"  ∫ {s} dx  =  {F}  + C"
      | .notElementary r =>
        IO.println s!"  ∫ {s} dx  — not elementary"
        IO.println s!"      ({r})"
      | .undecided r =>
        IO.println s!"  ∫ {s} dx  — undecided: {r}"
  IO.println ""

  IO.println "── Antiderivative self-checks ───────────────"
  let checks : List (String × Expr) := [
    ("x^2", x ^ (2 : Expr)),
    ("sin(x)", sin x),
    ("exp(x)", exp x),
    ("3x+1", (3 : Expr) * x + 1),
    ("1/x", x ^ ((-1 : Expr))),
    ("cos(2x)", cos ((2 : Expr) * x)),
  ]
  for (label, e) in checks do
    let ok := checkAntiderivative e "x"
    IO.println s!"  {if ok then "✓" else "✗"}  ∫ {label}  →  F' = f  is {ok}"
  IO.println ""

  IO.println "── Regression suite ─────────────────────────"
  IO.println (Regression.formatReport (Regression.runSuite))
  IO.println ""
  IO.println "Done.  Try:  lake exe taschenrechner 'diff sin(x^2)'"
  IO.println "       or:  lake exe taschenrechner --regression"

def runCommand (cmd : Command) : IO UInt32 := do
  match cmd with
  | .help =>
    IO.println helpText
    pure 0
  | .expr e =>
    IO.println s!"{e}"
    pure 0
  | .simplify e =>
    IO.println s!"{simplify e}"
    pure 0
  | .expand e =>
    IO.println s!"{expand e}"
    pure 0
  | .diff e v =>
    let d := diff e v
    IO.println s!"d/d{v} ({e})  =  {d}"
    pure 0
  | .integrate e v =>
    match integrate e v with
    | .success F src =>
      IO.println s!"∫ ({e}) d{v}  =  {F}  + C"
      IO.println s!"source: {src}  verified: {verifyDerivative F e v}"
      IO.println s!"check: d/d{v} = {diff F v}"
      pure 0
    | .notElementary r =>
      IO.eprintln s!"not elementary: {r}"
      pure 1
    | .failure r =>
      IO.eprintln s!"integration failed: {r}"
      pure 1

def runLine (line : String) : IO UInt32 := do
  match parseCommand line with
  | .ok cmd => runCommand cmd
  | .error err =>
    IO.eprintln s!"parse error: {err}"
    pure 1

/-- Read-eval-print loop. -/
private def trimLine (s : String) : String :=
  String.ofList (s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
    |>.reverse.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
    |>.reverse)

partial def repl : IO Unit := do
  IO.print "taschenrechner> "
  let line := trimLine (← (← IO.getStdin).getLine)
  if line.isEmpty then
    repl
  else if line == "quit" || line == "exit" || line == ":q" then
    IO.println "bye"
  else
    let _ ← runLine line
    repl

def usage : String :=
  "Usage:\n" ++
  "  taschenrechner                  run demo\n" ++
  "  taschenrechner <expr-or-cmd>    evaluate one expression/command\n" ++
  "  taschenrechner -c <cmd>         same as above\n" ++
  "  taschenrechner -i               interactive REPL\n" ++
  "  taschenrechner --regression     run 40-case integration suite\n" ++
  "  taschenrechner --matrix-regression  run matrix RREF/solve suite\n" ++
  "  taschenrechner --help           language help\n" ++
  "\n" ++
  "Examples:\n" ++
  "  taschenrechner 'x^2 + 2x + 1'\n" ++
  "  taschenrechner 'diff sin(x^2)'\n" ++
  "  taschenrechner 'int x*exp(x)'\n" ++
  "  taschenrechner 'diff(cos(2*x), x)'"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    runDemo
    pure 0
  | ["--help"] | ["-h"] | ["help"] =>
    IO.println helpText
    pure 0
  | ["--usage"] =>
    IO.println usage
    pure 0
  | ["--regression"] | ["-r"] =>
    Regression.runSuiteIO
  | ["--matrix-regression"] | ["--mat-regression"] | ["-mr"] =>
    MatrixRegression.runSuiteIO
  | ["-i"] | ["--repl"] =>
    IO.println "Taschenrechner REPL  (help | quit)"
    repl
    pure 0
  | ["-c", cmd] =>
    runLine cmd
  | "-c" :: _ =>
    IO.eprintln "option -c requires an argument"
    pure 2
  | cmd :: rest =>
    -- Only known flags are options; leading `-` may be unary minus (`-x^2`).
    if cmd == "-i" || cmd == "--repl" || cmd == "-h" || cmd == "--help"
        || cmd == "--usage" || cmd == "-c" || cmd == "--regression" || cmd == "-r"
        || cmd == "--matrix-regression" || cmd == "--mat-regression" || cmd == "-mr" then
      IO.eprintln s!"unknown option usage: {cmd}"
      IO.eprintln usage
      pure 2
    else
      -- join remaining args so shell-less use works: diff sin(x)
      let line := " ".intercalate (cmd :: rest)
      runLine line
