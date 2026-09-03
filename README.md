# Taschenrechner

A small **computer algebra system** written in [Lean 4](https://lean-lang.org/), supporting:

- Symbolic expression trees with exact rational coefficients (decimals like `1.5` → `3/2`)  
- **Numeric mode**: `N(sin(1), 6)` IEEE-754 binary64, then rounded to a rational (max 12 decimals)
- Algebraic simplification, expansion, **rewrite identities**, and **normal forms** (`cancel` / `together` / `nf`) over ℚ(x) and **ℚ(√d)(x)**
- **`factor` / `apart` / rational `int`** over **ℚ(√d)(x)** (linear/quadratic splitting, Hermite + partial fractions)
- **Hyperbolics** `sinh`/`cosh`/`tanh` and **`abs`**, with `hyperexpand`
- Inverse trig **`asin` / `acos` / `atan`** (`arcsin`/`arccos`/`arctan` aliases)
- Reciprocal trig **`sec` / `csc` / `cot`**, **factorial** (`n!`, `factorial`), **`gamma`**, **`floor`**, and **piecewise** (`if`/`ite`/`piecewise`)
- **Assumptions**: `assume(x>0)` refines `√(x²)` / `|x|`; `forget(x)`
- **Transcendental solve**: `solve(exp(x)=2)`, `solve(sin(x)=1/2)` (trig families in `k`)
- **Equations & inequalities**: `solve(x^2=4, x)` → `{2, -2}`; **cubics** (Cardano / `acos`); **quartics** (Ferrari); **irrational** `x^n=a`; **linear & polynomial systems** (2-var resultant, ≥3-var lex Gröbner); **intervals** `solve(x^2-1>0)`
- Textbook-style pretty-print: fractions, `√`, superscripts (`x²`), degree-sorted polys, `∞`
- **ASCII art** multi-line output for fractions, powers, matrices, and equations
- **Plotting** via **gnuplot**: `plot(sin(x))` drops into the gnuplot CLI; `plotpng(f)` writes a PNG
- **Substitution & evaluation**: `subst`, `eval` / `evalAt` over ℚ(i)
- **Factor & scalar solve**: rational roots, quadratic formula, `factor` / `roots` / `coeff`
- **Definite integrals** via FTC: `int(f, a, b)` / `int(f, x, a, b)`
- **Limits**: two-sided & one-sided, ±∞ (`oo`), pole order / `classify`; **series** for elementary 0/0 (`sin(x)/x`, `(e^x−1)/x`, …)
- **Radical integrals**: √(x²±a²), 1/√(a²−x²), … (verified)
- **Partial fractions**: `apart` / `pf`
- **Taylor / Maclaurin / Laurent series**: `taylor`, `series`, `laurent`, `seriesadd` / `seriesmul`
- Fraction-aware pretty-printing (`3/x`, `(1+2x)/(x+x²)`)
- Symbolic differentiation (product, chain, power, elementary functions)
- Symbolic indefinite & definite integration (table lookup, power rule, reverse chain rule, linear composites, integration by parts)
- Matrices: RREF, rank, nullspace, solve, **charpoly / eigenvalues / diagonalize / Jordan / expm**
- **Finite sums** `sum` (Faulhaber via Bernoulli, geometric, **Gosper** hypergeometric) and **ODEs** `dsolve` (1st-order linear / **Bernoulli** / separable, 2nd-order const-coeff including **`y''+y=sin(x)`**, linear systems via `expm`)
- Constant **`π`** (`pi`); trig `solve` families annotated **`k ∈ ℤ`**

## Build & run

```bash
lake build
lake exe taschenrechner                 # demo
lake exe taschenrechner 'x^2 + 2x + 1'  # parse & print (ASCII art when multi-line)
lake exe taschenrechner '(x^2+1)/(x-1)' # stacked fraction
lake exe taschenrechner 'diff sin(x^2)'
lake exe taschenrechner 'int x*exp(x)'
lake exe taschenrechner 'plot(sin(x))'           # plot + gnuplot CLI (needs gnuplot)
lake exe taschenrechner 'plotpng(sin(x), -6.28, 6.28)'  # → plot.png
lake exe taschenrechner -i              # REPL
lake exe taschenrechner --help          # language help

# Domain regression suites (also run as compile-time #guards)
lake exe taschenrechner --regression            # integration (~45 cases)
lake exe taschenrechner --matrix-regression     # matrices / eigen
lake exe taschenrechner --limit-regression      # limits / poles
lake exe taschenrechner --solve-regression      # factor / solve / apart
lake exe taschenrechner --sum-ode-regression    # sums / dsolve
lake exe taschenrechner --all-regression        # every suite + summary
```

Compile-time guard tests live in `Taschenrechner/Tests.lean` and each `*Regression.lean` module.

## Library overview

| Module | Role |
|--------|------|
| `Taschenrechner.Expr` | AST (`Expr`), `RatConst`, complex `CplxConst` / `i` |
| `Taschenrechner.AlgNum` | Multiquadratic algebraics `Σ c√κ`; `nf` / `factor` / `apart` / rational `int` over K(x) |
| `Taschenrechner.Complex` | Euler expand, `cis`, `evalCplx?` |
| `Taschenrechner.Matrix` | Matrix arithmetic, det, inv, transpose, trace |
| `Taschenrechner.LinAlg` | RREF, rank, nullspace, general `solve(A,b)` |
| `Taschenrechner.Eigen` | Charpoly, eigenvalues, diagonalize, Jordan, `expm` |
| `Taschenrechner.Simplify` | Constant folding, like-term collection, expand |
| `Taschenrechner.Rewrite` | Identity rewrite table (trig/hyperbolic/abs/exp) |
| `Taschenrechner.AsciiArt` | Multi-line ASCII layout (`asciiArt`, fractions/powers) |
| `Taschenrechner.Plot` | Sample curves and drive **gnuplot** (`plot` CLI / `plotpng`) |
| `Taschenrechner.Normal` | `cancel`, `together`, `normalForm`, stronger zero tests |
| `Taschenrechner.Eval` | `subst`, `eval?`, `evalAt`, exact eval over ℚ(i) |
| `Taschenrechner.Numeric` | `N(e[, digits])` float evaluation → rounded rational |
| `Taschenrechner.Solve` | `factor`, scalar/system/inequality/`bivariate` `solve`, cubics, quartics, `roots` |
| `Taschenrechner.BiPoly` | Bivariate polys + Sylvester resultant (2-var elimination) |
| `Taschenrechner.Groebner` | Multivariate lex Gröbner bases (Buchberger); `groebner` / multi-var `solve` |
| `Taschenrechner.Series` | Taylor / Maclaurin / Laurent + truncated series arithmetic |
| `Taschenrechner.Limit` | Limits (two-sided/one-sided, poles, `classify`, series at 0/∞) |
| `Taschenrechner.Gosper` | Hypergeometric summation (Gosper); `sum` of rationals and `p(k)·r^k` |
| `Taschenrechner.Sum` | Finite sums (Faulhaber / Bernoulli, geometric, Gosper) |
| `Taschenrechner.ODE` | `dsolve`: 1st-order linear / Bernoulli / separable, 2nd-order const-coeff + nonhomogeneous `sin`/`cos`, systems `Y'=AY` |
| `Taschenrechner.Diff` | `diff`, `diffN`, partials |
| `Taschenrechner.Trig` | Trig preprocess (product-to-sum, power-reduce) + linear integrals |
| `Taschenrechner.Poly` | Univariate polynomials over ℚ |
| `Taschenrechner.RatInt` | Rational integration + `apart` (partial fractions) |
| `Taschenrechner.Risch` | Transcendental Risch (exp/log/trig, non-existence) |
| `Taschenrechner.AlgRisch` | Algebraic Risch: `R(x, √p(x))` with deg p ≤ 2 (Euler) |
| `Taschenrechner.Integrate` | Structured `IntegrateResult`, verified `integrate` |
| `Taschenrechner.Parse` | Lexer + recursive-descent parser (`parse`, `parseCommand`) |
| `Taschenrechner.Env` | REPL bindings, `ans`, session save/load |
| **Regression modules** | |
| `…Regression` | Integration (`--regression`) |
| `…MatrixRegression` | Matrices / eigen (`--matrix-regression`) |
| `…LimitRegression` | Limits / poles (`--limit-regression`) |
| `…SolveRegression` | Factor / solve / apart (`--solve-regression`) |
| `…SumODERegression` | Sums / ODEs (`--sum-ode-regression`) |
| `…AllRegression` | Master runner (`--all-regression`) |

## Expression language

```
x^2 + 3*x + 1
0.5                  # decimal → exact 1/2 (prints as 0.5)
1.25 + 0.75          # → 2
2x(x+1)              # juxtaposition = multiply
sin(x^2)
asin(x)  acos(x)  atan(x)
sec(x)  csc(x)  cot(x)
sinh(x)  cosh(x)  tanh(x)
5!                   # postfix factorial; also factorial(n)
gamma(x)             # Γ(n)=(n-1)!, Γ(1/2)=√π
floor(x)
if(x>0, x, -x)       # piecewise: if / ite / piecewise(c1,v1,…,default)
abs(x)               # |x|;  cabs(z) for √(re²+im²)
rewrite(e)           # apply identity table
hyperexpand(sinh(x)) # → (e^x − e^{-x})/2
-x^2 + 1             # unary minus; ^ binds tighter → -(x^2)
2+3*i                # complex rationals ℚ(i)
N(sin(1), 4)         # → 0.8415  (numeric approx)
N(sqrt(2))           # → 1.414214 (default 6 digits)
euler(exp(i*x))      # → cos(x) + i·sin(x)
[1, 2; 3, 4]         # 2×2 matrix
det([1, 2; 3, 4])    # −2
inv([1, 2; 0, 1])    # inverse
rref([1, 2; 2, 4])   # reduced row echelon form
nullspace([1, 2; 2, 4])      # → [-2; 1]
solve([1, 1; 0, 1], [3; 2])  # → [1; 2]
solve([1, 2; 2, 4], [3; 6])  # → [3-2·t1; t1]
solve(x^2=4, x)              # → {2, -2}
solve(2*x+1=0)               # → {-1/2}
solve(x+y=1, x-y=3)          # → x = 2, y = -1
solve(x^2-1>0)               # → (-∞, -1) ∪ (1, ∞)
solve(x^2-1>=0)              # → (-∞, -1] ∪ [1, ∞)
charpoly([1, 0; 0, 2])       # → t² − 3·t + 2
eigvals([1, 0; 0, 2])        # → [1, 2]
eigenspace([1, 0; 0, 2], 2)  # → [0; 1]
[1, 2; 3, 4]*eye(2)  # matrix product
diff(sin(x^2), x)    # CAS forms inside expressions
int(x*exp(x))
```

Commands: `name := <expr>`, `vars`, `clear [name]`, `diff`, `int`, `simplify`, `expand`, `cancel`, `together`, `nf`/`normal`, `sum`, `dsolve`, `limit`/`limleft`/`limright`, `apart`, `help`.

**Normal forms**

| Form | What it does |
|------|----------------|
| `cancel(e)` | Cancel common factors in products/quotients (integer powers + poly GCD for rationals) |
| `together(e)` | Put a sum of rationals over a common denominator (`RatFn`) |
| `nf(e)` / `normal(e)` | `simplify` → `cancel` → `together` over **ℚ(x)** or a multiquadratic **K(x)** (e.g. ℚ(√2)) |

```bash
lake exe taschenrechner 'cancel((x^2-1)/(x-1))'   # → 1 + x
lake exe taschenrechner 'together(1/x + 1/(x+1))' # → (1+2x)/(x+x²)
lake exe taschenrechner 'nf(1/x + 2/x)'           # → 3/x
lake exe taschenrechner 'nf((x+sqrt(2))*(x-sqrt(2)))'  # → x² − 2
lake exe taschenrechner 'nf(1/sqrt(2))'           # → √2 / 2
lake exe taschenrechner 'nf((sqrt(2)*x+2)/(x+sqrt(2)))'  # → √2
lake exe taschenrechner 'subst(x^2+1, x, 3)'      # → 10
lake exe taschenrechner 'eval(x^2+1, x, 4)'       # → 17
lake exe taschenrechner 'eval(2+3*i)'             # → 2+3*i
```

**Substitution & evaluation**

| Form | What it does |
|------|----------------|
| `subst(e, v, a)` / `subs(...)` | Replace free `v` by `a`, then simplify |
| `eval(e)` | Exact eval in ℚ(i) when ground; else simplify |
| `eval(e, v, a)` / `at(e, v, a)` | Substitute then exact-eval if possible |
| `N(e)` / `numeric(e)` | IEEE-754 binary64 eval, then round to a rational (default 6 decimals) |
| `N(e, n)` | Same with `n` places after the decimal (**max 12**); ties away from 0 |

Decimals (`1.5`, `.25`) parse as exact rationals. Rationals whose denominator is `2^a·5^b` print as decimals (e.g. `1/2` → `0.5`); others stay as fractions (`1/3`).

**Factor, solve, systems & inequalities**

| Form | What it does |
|------|----------------|
| `factor(e[, v])` | Factor poly/rational over ℚ or ℚ(√d); integers → `[prime, exp; …]` matrix |
| `roots(e[, v])` | Roots of `e=0` as a 1×n matrix (rational, quadratic, cubic, quartic) |
| `solve(f[, x])` | Roots of scalar `f=0`; also `solve(A,b)` for matrices |
| `solve(lhs=rhs[, x])` | Equation form (preferred) |
| `solve(lhs, rhs, x)` | Solve `lhs = rhs` (3-arg form) |
| `solve(eq1, eq2, …[, x, y, …])` | **System**: linear via RREF; 2-var polynomial via resultant; ≥3-var via lex Gröbner |
| `groebner(eq, …)` / `gb(...)` | Lex Gröbner basis (column of generators); optional trailing variable order |
| `solve(expr ? 0)` / `solve(a ? b)` | **Inequality** → merged intervals with open/closed ends; print as `(-∞, -1) ∪ [1, ∞)` |
| `collect(e[, v])` | Rewrite as canonical poly/rational in `v` |
| `coeff(e, n)` / `coeff(e, v, n)` | Coefficient of `v^n` |

Relations parse at top level: `a = b`, `a < b`, `a <= b` / `a ≤ b`, `a > b`, `a >= b` / `a ≥ b` (`>`/`≥` normalize to flipped `<`/`≤`). Linear systems use RREF; polynomial systems use resultants (2-var) or lex Gröbner (≥3-var). Inequalities are univariate polynomial. Internally intervals are n×4 rows `[lo, hi, loClosed, hiClosed]` (CLI pretty-prints unions); whole line → `ℝ`, empty → `∅`, scalar roots → `{…}`.

```bash
lake exe taschenrechner 'factor(x^2-1)'              # → (x-1)(x+1)
lake exe taschenrechner 'factor(x^2-2)'              # → (x−√2)(x+√2)
lake exe taschenrechner 'factor(x^2-2*sqrt(2)*x+2)'  # → (x−√2)²
lake exe taschenrechner 'apart((x+sqrt(2))/(x^2-2))' # → 1/(x−√2)
lake exe taschenrechner 'solve(x^2=4, x)'             # → {2, -2}
lake exe taschenrechner 'solve(x^3-2=0, x)'           # → 2^{1/3} and complex cube roots
lake exe taschenrechner 'solve(x^3-3*x-1=0, x)'       # → 2 cos((acos(1/2) − 2πk)/3)
lake exe taschenrechner 'solve(x^4+1=0, x)'            # → four Ferrari roots
lake exe taschenrechner 'solve(x^4+x+1=0, x)'          # → four Ferrari roots
lake exe taschenrechner 'int(1/sqrt(1-x^2))'           # → asin(x)
lake exe taschenrechner 'assume(x>0); sqrt(x^2)'        # → x
lake exe taschenrechner 'solve(exp(x)=2)'               # → {ln(2)}
lake exe taschenrechner 'solve(sin(x)=1/2)'             # → asin(1/2)+2πk, …
lake exe taschenrechner '5!'                            # → 120
lake exe taschenrechner 'gamma(1/2)'                    # → √π
lake exe taschenrechner 'if(x>0, x, -x)'                # piecewise
lake exe taschenrechner 'int(sec(x))'                   # → ln(sec x + tan x)
lake exe taschenrechner 'solve(x^2-5*x+6=0, x)'       # → {3, 2}
lake exe taschenrechner 'solve(x^2, 4, x)'            # → {2, -2}  (3-arg form)
lake exe taschenrechner 'solve(x+y=1, x-y=3)'         # → x = 2, y = -1
lake exe taschenrechner 'solve(x^2=1, y^2=1, z=x+y)'   # → four points via Gröbner
lake exe taschenrechner 'groebner(x-1, x^2+y)'         # → x − 1, y + 1
lake exe taschenrechner 'solve(x+y+z=6, x-y=1, y-z=1)' # → x = 3, y = 2, z = 1
lake exe taschenrechner 'solve(x^2+y^2=1, x+y=1)'     # → {x=1,y=0}, {x=0,y=1}
lake exe taschenrechner 'solve(y=x^2, x+y=2)'         # → {x=1,y=1}, {x=-2,y=4}
lake exe taschenrechner 'solve(x^2-1>0)'              # → (-∞, -1) ∪ (1, ∞)
lake exe taschenrechner 'solve(x^2-1>=0)'             # → (-∞, -1] ∪ [1, ∞)
lake exe taschenrechner 'solve(x^2-1<0)'              # → (-1, 1)
lake exe taschenrechner 'coeff(3*x^2+2*x+1, 2)'       # → 3
```

**Characteristic polynomial, diagonalize & expm**

| Form | What it does |
|------|----------------|
| `charpoly(A)` / `charpoly(A, t)` | `det(t I − A)` (monic char poly) |
| `eigvals(A)` / `eigen(A)` / `eig(A)` | Eigenvalues as a 1×k row (rational + quadratic) |
| `eigenspace(A, λ)` / `eigvec(A, λ)` | Nullspace basis of `A − λI` |
| `diagonalize(A)` | `[P, D]` with `P⁻¹ A P = D` (when diagonalizable) |
| `jordan(A)` / `jf(A)` | `[P, J]` Jordan form (`P⁻¹ A P = J`; defective OK if charpoly splits) |
| `modal(A)` / `diagform(A)` | Just `P` or just `D` (diagonalizable) |
| `expm(A)` | `P exp(J) P⁻¹` via Jordan form (defective OK) |

```bash
lake exe taschenrechner 'charpoly([1, 0; 0, 2])'      # → t² − 3t + 2
lake exe taschenrechner 'eigvals([0, -1; 1, 0])'       # → [-i, i]
lake exe taschenrechner 'eigenspace([1, 0; 0, 2], 2)' # → [0; 1]
lake exe taschenrechner 'diagform([1, 0; 0, 2])'       # → diag(1,2) (order may vary)
lake exe taschenrechner 'expm(zeros(2))'              # → I
lake exe taschenrechner 'expm([0, 1; 0, 0])'           # → [1, 1; 0, 1]  (Jordan)
lake exe taschenrechner 'jordan([0, 1; 0, 0])'         # → [P, J]
```

**Finite sums & ODEs**

| Form | What it does |
|------|----------------|
| `sum(expr, k, lo, hi)` | ∑_{k=lo}^{hi} expr (Faulhaber via Bernoulli for all `k^m`; geometric; **Gosper** for hypergeometric `t(k)`; **numeric** if bounds are ints) |
| `sum(k, lo, hi, expr)` | Same, index-first order |
| `dsolve(eq)` | 1st-order linear / Bernoulli `y'+P y=Q y^n` / separable; 2nd-order const-coeff (`y''`/`ypp`); `g(x)=sin/cos` via undetermined coeff / VoP |
| `dsolve(eq, y, x)` | Specify unknown and independent variable |
| `dsolve(eq, x0, y0)` | IC y(x0)=y0 (first-order) |
| `dsolve(eq, x0, y0, yp0)` | ICs y(x0)=y0, y′(x0)=yp0 (second-order) |
| `dsolve(eq, y, x, x0, y0[, yp0])` | Full IC form |
| `dsolve(A)` | Linear system **Y′ = A Y** → `yᵢ = (Φ(x)·C)ᵢ`, Φ=expm(A x) |
| `dsolve(A, Y0)` | System with Y(0)=Y0 |
| `C` / `C1`,`C2` | Arbitrary constants (fixed by ICs) |

Linear 1st-order: `y' + P(x)*y = Q(x)`. Bernoulli: `y' + P y = Q y^n` (`v = y^{1−n}`). Separable: `y' = f(x)*g(y)`. Const-coeff 2nd-order: `a y'' + b y' + c y = g` (g constant). Systems `Y'=AY` use Jordan `expm` (defective OK).

```bash
lake exe taschenrechner 'sum(k, 1, n, k)'              # → n(n+1)/2
lake exe taschenrechner 'sum(k, 1, 10, k)'             # → 55
lake exe taschenrechner 'sum(k^7, k, 1, n)'            # Faulhaber (Bernoulli)
lake exe taschenrechner 'sum(k^10, k, 1, 5)'           # numeric via closed form
lake exe taschenrechner 'sum(1/(k*(k+1)), k, 1, n)'    # Gosper → n/(n+1)
lake exe taschenrechner 'sum(k*2^k, k, 1, n)'          # Gosper → (n−1)2^{n+1}+2
lake exe taschenrechner 'dsolve(y'\'' + y = 0)'         # → y = C·exp(-x)
lake exe taschenrechner 'dsolve(y'\'' + y = x)'         # → y = C·exp(-x) + x − 1
lake exe taschenrechner 'dsolve(yp + y = 0, 0, 1)'     # → y = exp(-x)
lake exe taschenrechner 'dsolve(yp = x*y)'             # → y = C·exp(x²/2)
lake exe taschenrechner 'dsolve(yp = y^2)'             # Bernoulli → y = 1/(C − x)
lake exe taschenrechner 'dsolve(yp + y/x = y^2)'       # Bernoulli n=2
lake exe taschenrechner "dsolve(y'' + y = 0)"          # → y = C1·cos(x) + C2·sin(x)
lake exe taschenrechner "dsolve(y'' + y = sin(x))"     # → y = C1·cos(x) + C2·sin(x) − (x/2)·cos(x)
lake exe taschenrechner 'solve(sin(x)=0)'              # → {k·π}, k ∈ ℤ
lake exe taschenrechner 'pi'                           # → π
lake exe taschenrechner "dsolve(y'' + y = 0, 0, 1, 0)" # → y = cos(x)
lake exe taschenrechner 'dsolve([1,0;0,2])'            # → y1 = C1·exp(x), y2 = C2·exp(2x)
lake exe taschenrechner 'dsolve([1,0;0,2],[3;4])'      # → y1 = 3·exp(x), y2 = 4·exp(2x)
lake exe taschenrechner 'dsolve([0,1;0,0])'            # → y1 = C1 + C2·x, y2 = C2
```

**Limits & radical integrals**

| Form | What it does |
|------|----------------|
| `limit(e, a)` / `lim(e, a)` | two-sided lim_{x→a} e |
| `limit(e, x, a)` | free variable `x` |
| `limit(e, a, 1)` / `limright(e, a)` | right-hand limit a⁺ |
| `limit(e, a, -1)` / `limleft(e, a)` | left-hand limit a⁻ |
| `poleorder(e, a)` | order of pole at `a` (0 if not a pole) |
| `classify(e, a)` | removable / continuous / pole `[k, lim-, lim+]` |
| `a = oo` / `-oo` | +∞ / −∞ |

```bash
lake exe taschenrechner 'limit((x^2-1)/(x-1), 1)'   # → 2  (removable)
lake exe taschenrechner 'limit(sin(x)/x, 0)'         # → 1  (series)
lake exe taschenrechner 'limit((1-cos(x))/x^2, 0)'   # → 1/2
lake exe taschenrechner 'limit((1+1/x)^x, oo)'       # → e
lake exe taschenrechner 'limright(1/x, 0)'           # → +∞
lake exe taschenrechner 'limleft(1/x, 0)'            # → -∞
lake exe taschenrechner 'poleorder(1/x^2, 0)'        # → 2
lake exe taschenrechner 'classify(1/x, 0)'           # → [1, -∞, +∞]
lake exe taschenrechner 'limit(1/x, oo)'            # → 0
lake exe taschenrechner 'int(1/sqrt(x^2+1))'        # → ln(x + √(x²+1))
lake exe taschenrechner 'apart(1/((x-1)*(x-2)))'    # → 1/(x-2) − 1/(x-1)
```

**Definite integrals & series**

| Form | What it does |
|------|----------------|
| `int(f, a, b)` | Definite ∫_a^b f(x) dx (FTC) |
| `int(f, x, a, b)` | Definite in free variable `x` |
| `taylor(f, n)` | Maclaurin poly of degree ≤ n in `x` |
| `taylor(f, x, a, n)` | Taylor about `a` |
| `series(f, n)` / `maclaurin(f, n)` | Same as Maclaurin |
| `laurent(f, n)` | Laurent about 0 through degree n (rationals exact) |
| `laurent(f, a, n)` / `laurent(f, x, a, n)` | Laurent about `a` |
| `seriesadd(f, g, n)` / `sadd(...)` | Truncated sum of series about 0 |
| `seriesmul(f, g, n)` / `smul(...)` | Truncated product of series about 0 |

```bash
lake exe taschenrechner 'int(x^2, 0, 1)'             # → 1/3
lake exe taschenrechner 'int(sin(x), 0, 0)'           # → 0
lake exe taschenrechner 'taylor(exp(x), 3)'           # → 1 + x + x²/2 + x³/6
lake exe taschenrechner 'series(sin(x), 5)'           # → x − x³/6 + x⁵/120
lake exe taschenrechner 'laurent(1/x^2, 1)'           # → 1/x²
lake exe taschenrechner 'laurent(1/(1-x), 3)'         # → 1 + x + x² + x³
lake exe taschenrechner 'laurent(1/(x-1), 1, 2)'      # → 1/(x−1)
lake exe taschenrechner 'seriesmul(1/(1-x), 1/(1-x), 3)' # → 1 + 2x + 3x² + 4x³
```

**Plotting (gnuplot)**

Requires [`gnuplot`](http://www.gnuplot.info/) on `PATH`. On a terminal, `plot` / `plot(f)` **starts gnuplot and feeds commands on stdin**, then a `gnuplot>` prompt forwards further lines. Type any gnuplot command (`set xrange [-5:5]`, `replot`, `set title "…"`, `help`, …); `quit` or `exit` returns to the CAS (or the shell). `plotpng` writes a PNG via `pngcairo` and does not enter the CLI.

When the expression only uses gnuplot-supported ops (`+ − * / ^`, `sin/cos/tan`, `sinh/cosh/tanh`, `exp`, `ln`→`log`, `atan`, `abs`, `sqrt`), Taschenrechner sends a **native formula** (`plot sin(x)`). Otherwise it **samples** the expression in Lean and plots the data file.

**No x-range is forced** in the gnuplot script (gnuplot’s default axes / autoscale). Optional `a,b` only set the Lean sampling window used if a data fallback is needed (default sample window `[-10,10]`). Without a TTY (pipes / CI), interactive plots detach as before (`persist` + `pause mouse close`).

| Form | Meaning |
|------|---------|
| `plot` / `plot()` / `gnuplot` | Bare gnuplot CLI (no curve) |
| `plot(f)` | Plot `f` vs `x`, then gnuplot CLI |
| `plot(f, a, b)` | Optional sample window `[a,b]` for data fallback |
| `plot(f, x, a, b)` | Free variable `x` |
| `plot(f, a, b, n)` | `n` samples / gnuplot `set samples` |
| `plotpng(f)` | Write `plot.png` (no CLI) |
| `plotpng(f, a, b)` | PNG; `a,b` only for sample fallback |
| `plotpng(f, name, a, b)` | PNG `name.png` |

```bash
lake exe taschenrechner 'plot(sin(x))'                 # native + gnuplot>
lake exe taschenrechner plot                           # empty gnuplot shell
lake exe taschenrechner 'plot(x^2)'
lake exe taschenrechner 'plot(exp(-x^2))'
lake exe taschenrechner 'plotpng(sin(x)*exp(-x/4))'
```

```bash
lake exe taschenrechner -i
taschenrechner> A := [1, 2; 3, 4]; b := [5; 11]
taschenrechner> solve(A, b)
taschenrechner> ans
taschenrechner> save session.tr
taschenrechner> clear
taschenrechner> load session.tr
taschenrechner> vars
```

## Quick examples

```lean
import Taschenrechner
open Taschenrechner.Expr
open Taschenrechner.Parse

#eval parse "diff(sin(x^2), x)"
-- ok (2·x·cos(x^2))

#eval parse "int(x*exp(x))"
-- ok (-(exp(x)) + x·exp(x))

-- programmatic API still available:
#eval diff (x ^ (3 : Expr) + sin x) "x"
#eval integrateDefinite (x ^ (2 : Expr)) "x" 0 1
```

## Supported calculus (representative)

**Differentiation:** constants, polynomials, `sin`/`cos`/`tan`/`atan`, `exp`, `ln`, products, quotients (as `a·b⁻¹`), general powers.

**Integration** — two layers:

1. **Risch** (`risch` / first stage of `integrate`)
   - Complete **rational** case over ℚ(x): division, Hermite reduction, partial fractions, Rothstein–Trager residues, `atan` for irreducible quadratics
   - **Trig preprocessing**: `tan→sin/cos`, `sin²`/`cos²` power-reduction, product-to-sum; linear `sin`/`cos`/`tan(ax+b)`
   - **Exponential** monomials `r(x)·exp(p(x))` via the Risch differential equation `v' + p'v = r`
   - **Complex scalars / exp**: `(a+bi)·f`, `exp((α+βi)x)` e.g. `∫ exp(i x) = -i exp(i x)`; `re`/`im`/`conj` of real-linear complex expressions
   - **Non-existence certificates**, e.g. `∫ exp(x²) dx` is not elementary; `∫ x·exp(x²) dx = ½ exp(x²)` is
   - Simple log patterns (`ln(x)^n / x`, `ln(x)^n`)
   - **Algebraic** `R(x, √p(x))` with deg p ≤ 2: Euler substitution to a rational in K(t)
2. **Heuristics** (if Risch returns undecided): reverse chain rule for non-linear args, by-parts

**Not fully covered:** nested towers (`√(x+√2)` as a *second* radical in x), algebraic curves of genus ≥ 1 (`√(x³+…)`), special functions beyond elementary. Rational functions over a *constant* multiquadratic field ℚ(√d) are handled (`factor` / `apart` / `int`).

```bash
lake exe taschenrechner 'int 1/(x^2+1)'   # atan(x)
lake exe taschenrechner 'int 1/(x^2-2)'    # logs in (x±√2)
lake exe taschenrechner 'int 1/(x-sqrt(2))'
lake exe taschenrechner 'int sqrt(x+1)'
lake exe taschenrechner 'int 1/sqrt(x^2+x+1)'
lake exe taschenrechner 'int exp(x^2)'     # not elementary (Risch)
lake exe taschenrechner 'int x*exp(x^2)'   # 1/2·exp(x^2)
```
