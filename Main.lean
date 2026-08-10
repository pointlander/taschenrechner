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

def printExpr (e : Expr) : IO Unit := do
  -- Prefer solution pretty-print (named systems, intervals, root sets).
  let sol := prettySolution e
  if sol != Expr.toString e then
    IO.println sol
  else
    match asMat? e with
    | some rows =>
      for line in (Mat.pretty rows).splitOn "\n" do
        IO.println line
    | none =>
      IO.println s!"{e}"

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

  IO.println "── Integration regression (summary) ─────────"
  let intR := Regression.runSuite
  IO.println s!"  {Regression.passCount intR}/{intR.length} integration cases"
  IO.println "  Full report:  lake exe taschenrechner --all-regression"
  IO.println ""
  IO.println "Done.  Try:  lake exe taschenrechner -i"
  IO.println "       A := [1, 2; 3, 4]   then   det(A)"

/-- Record a successful value as `ans`. -/
def withAns (env : Env) (val : Expr) : Env :=
  Env.setAns env val

/-- Trim whitespace (used by load and REPL). -/
def trimLine (s : String) : String :=
  String.ofList (s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
    |>.reverse.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
    |>.reverse)

/-- Run a command under `env`; returns exit code and updated environment. -/
def runCommand (env : Env) (cmd : Command) : IO (UInt32 × Env) := do
  match cmd with
  | .help =>
    IO.println helpText
    pure (0, env)
  | .vars =>
    IO.println (Env.format env)
    pure (0, env)
  | .clearAll =>
    IO.println "(cleared all bindings)"
    pure (0, Env.empty)
  | .clearOne name =>
    if (env.get? name).isSome then
      IO.println s!"(cleared {name})"
      pure (0, env.erase name)
    else
      IO.eprintln s!"clear: '{name}' is not bound"
      pure (1, env)
  | .save path =>
    try
      IO.FS.writeFile path (Env.toSession env)
      IO.println s!"(saved {env.size} binding(s) to {path})"
      pure (0, env)
    catch e =>
      IO.eprintln s!"save failed: {e}"
      pure (1, env)
  | .load path =>
    try
      let text ← IO.FS.readFile path
      let mut env' := Env.empty
      let mut nLoaded : Nat := 0
      for raw in text.splitOn "\n" do
        let line := trimLine raw
        if line.isEmpty then pure ()
        else if line.startsWith "#" then pure ()
        else
          match parseCommand line env' with
          | .ok (.assign name rhs) =>
            match envAssign env' name rhs with
            | .ok (e, _) =>
              env' := e
              nLoaded := nLoaded + 1
            | .error err =>
              throw (IO.userError s!"load {path}: {err} (while binding {name})")
          | .ok _ =>
            throw (IO.userError s!"load {path}: expected assignment, got: {line}")
          | .error err =>
            throw (IO.userError s!"load {path}: {err} (line: {line})")
      IO.println s!"(loaded {nLoaded} binding(s) from {path})"
      pure (0, env')
    catch e =>
      IO.eprintln s!"load failed: {e}"
      pure (1, env)
  | .assign name rhs =>
    match envAssign env name rhs with
    | .error err =>
      IO.eprintln s!"assign error: {err}"
      pure (1, env)
    | .ok (env', val) =>
      IO.print s!"{name} := "
      printExpr val
      pure (0, withAns env' val)
  | .expr e =>
    let e := simplify (substEnv env e)
    printExpr e
    pure (0, withAns env e)
  | .simplify e =>
    let e := simplify (substEnv env e)
    printExpr e
    pure (0, withAns env e)
  | .expand e =>
    let e := expand (substEnv env e)
    printExpr e
    pure (0, withAns env e)
  | .cancel e =>
    let e := Expr.cancel (substEnv env e)
    printExpr e
    pure (0, withAns env e)
  | .together e =>
    let e := Expr.together (substEnv env e)
    printExpr e
    pure (0, withAns env e)
  | .normal e =>
    let e := Expr.normalForm (substEnv env e)
    printExpr e
    pure (0, withAns env e)
  | .diff e v =>
    let e := simplify (substEnv env e)
    let d := diff e v
    IO.println s!"d/d{v} ({e})  =  {d}"
    pure (0, withAns env d)
  | .integrate e v =>
    let e := simplify (substEnv env e)
    match integrate e v with
    | .success F src =>
      IO.println s!"∫ ({e}) d{v}  =  {F}  + C"
      IO.println s!"source: {src}  verified: {verifyDerivative F e v}"
      IO.println s!"check: d/d{v} = {diff F v}"
      pure (0, withAns env F)
    | .notElementary r =>
      IO.eprintln s!"not elementary: {r}"
      pure (1, env)
    | .failure r =>
      IO.eprintln s!"integration failed: {r}"
      pure (1, env)

/-- Run one statement (no `;` splitting). -/
def runStatement (env : Env) (stmt : String) : IO (UInt32 × Env) := do
  match parseCommand stmt env with
  | .ok cmd => runCommand env cmd
  | .error err =>
    IO.eprintln s!"parse error: {err}"
    pure (1, env)

/-- Run a line, possibly with multiple top-level `;`-separated statements. -/
def runLine (env : Env) (line : String) : IO (UInt32 × Env) := do
  let stmts := splitStatements line
  if stmts.isEmpty then
    pure (0, env)
  else
    let mut env := env
    let mut code : UInt32 := 0
    for stmt in stmts do
      let (c, env') ← runStatement env stmt
      env := env'
      code := c
      -- continue after errors so later stmts still see prior successful binds
    pure (code, env)

partial def repl (env : Env) : IO Unit := do
  IO.print "taschenrechner> "
  let line := trimLine (← (← IO.getStdin).getLine)
  if line.isEmpty then
    repl env
  else if line == "quit" || line == "exit" || line == ":q" then
    IO.println "bye"
  else
    let (_code, env') ← runLine env line
    repl env'

def usage : String :=
  "Usage:\n" ++
  "  taschenrechner                  run demo\n" ++
  "  taschenrechner <expr-or-cmd>    evaluate one expression/command\n" ++
  "  taschenrechner -c <cmd>         same as above\n" ++
  "  taschenrechner -i               interactive REPL (with bindings)\n" ++
  "  taschenrechner --regression     integration suite (~45 cases)\n" ++
  "  taschenrechner --matrix-regression   matrix / eigen suite\n" ++
  "  taschenrechner --limit-regression    limits / poles\n" ++
  "  taschenrechner --solve-regression    factor / solve / apart\n" ++
  "  taschenrechner --sum-ode-regression  sums / first-order ODEs\n" ++
  "  taschenrechner --all-regression      every domain suite\n" ++
  "  taschenrechner --help           language help\n" ++
  "\n" ++
  "REPL:\n" ++
  "  A := [1, 2; 3, 4]; det(A)\n" ++
  "  ans                   last result\n" ++
  "  vars | clear [name]\n" ++
  "  save file.tr | load file.tr\n" ++
  "\n" ++
  "Examples:\n" ++
  "  taschenrechner 'x^2 + 2x + 1'\n" ++
  "  taschenrechner 'diff sin(x^2)'\n" ++
  "  taschenrechner 'int x*exp(x)'\n" ++
  "  taschenrechner 'sum(k, 1, n, k)'\n" ++
  "  taschenrechner 'dsolve(yp + y = 0)'\n" ++
  "  taschenrechner 'A := eye(2); det(A)'"

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
  | ["--limit-regression"] | ["-lr"] =>
    LimitRegression.runSuiteIO
  | ["--solve-regression"] | ["-sr"] =>
    SolveRegression.runSuiteIO
  | ["--sum-ode-regression"] | ["--ode-regression"] | ["-sor"] =>
    SumODERegression.runSuiteIO
  | ["--all-regression"] | ["-ar"] | ["--regressions"] =>
    AllRegression.runSuiteIO
  | ["-i"] | ["--repl"] =>
    IO.println "Taschenrechner REPL  (help | vars | clear | save | load | quit)"
    IO.println "  name := expr   |   stmt; stmt   |   ans   |   save/load file"
    repl Env.empty
    pure 0
  | ["-c", cmd] =>
    let (code, _) ← runLine Env.empty cmd
    pure code
  | "-c" :: _ =>
    IO.eprintln "option -c requires an argument"
    pure 2
  | cmd :: rest =>
    if cmd == "-i" || cmd == "--repl" || cmd == "-h" || cmd == "--help"
        || cmd == "--usage" || cmd == "-c" || cmd == "--regression" || cmd == "-r"
        || cmd == "--matrix-regression" || cmd == "--mat-regression" || cmd == "-mr"
        || cmd == "--limit-regression" || cmd == "-lr"
        || cmd == "--solve-regression" || cmd == "-sr"
        || cmd == "--sum-ode-regression" || cmd == "--ode-regression" || cmd == "-sor"
        || cmd == "--all-regression" || cmd == "-ar" || cmd == "--regressions" then
      IO.eprintln s!"unknown option usage: {cmd}"
      IO.eprintln usage
      pure 2
    else
      let line := " ".intercalate (cmd :: rest)
      let (code, _) ← runLine Env.empty line
      pure code
