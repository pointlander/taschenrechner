# Taschenrechner

A small **computer algebra system** written in [Lean 4](https://lean-lang.org/), supporting:

- Symbolic expression trees with exact rational coefficients  
- Algebraic simplification, expansion, and **normal forms** (`cancel` / `together` / `nf`)
- **Equations & inequalities**: `solve(x^2=4, x)` → `{2, -2}`; **systems** `solve(x+y=1,x-y=3)` → `x = 2, y = -1`; **intervals** `solve(x^2-1>0)` → `(-∞, -1) ∪ (1, ∞)`
- Textbook-style pretty-print: fractions, `√`, superscripts (`x²`), degree-sorted polys, `∞`
- **Substitution & evaluation**: `subst`, `eval` / `evalAt` over ℚ(i)
- **Factor & scalar solve**: rational roots, quadratic formula, `factor` / `roots` / `coeff`
- **Definite integrals** via FTC: `int(f, a, b)` / `int(f, x, a, b)`
- **Limits**: two-sided & one-sided, ±∞ (`oo`), pole order / `classify`
- **Radical integrals**: √(x²±a²), 1/√(a²−x²), … (verified)
- **Partial fractions**: `apart` / `pf`
- **Taylor / Maclaurin / Laurent series**: `taylor`, `series`, `laurent`, `seriesadd` / `seriesmul`
- Fraction-aware pretty-printing (`3/x`, `(1+2x)/(x+x²)`)
- Symbolic differentiation (product, chain, power, elementary functions)
- Symbolic indefinite & definite integration (table lookup, power rule, reverse chain rule, linear composites, integration by parts)
- Matrices: RREF, rank, nullspace, solve, **charpoly / eigenvalues / diagonalize / expm**
- **Finite sums** `sum` (Faulhaber + geometric) and **ODEs** `dsolve` (1st-order, 2nd-order const-coeff, linear systems via `expm`)

## Build & run

```bash
lake build
lake exe taschenrechner                 # demo
lake exe taschenrechner 'x^2 + 2x + 1'  # parse & print
lake exe taschenrechner 'diff sin(x^2)'
lake exe taschenrechner 'int x*exp(x)'
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
| `Taschenrechner.Complex` | Euler expand, `cis`, `evalCplx?` |
| `Taschenrechner.Matrix` | Matrix arithmetic, det, inv, transpose, trace |
| `Taschenrechner.LinAlg` | RREF, rank, nullspace, general `solve(A,b)` |
| `Taschenrechner.Eigen` | Charpoly, eigenvalues, diagonalize, `expm` |
| `Taschenrechner.Simplify` | Constant folding, like-term collection, expand |
| `Taschenrechner.Normal` | `cancel`, `together`, `normalForm`, stronger zero tests |
| `Taschenrechner.Eval` | `subst`, `eval?`, `evalAt`, exact eval over ℚ(i) |
| `Taschenrechner.Solve` | `factor`, scalar/`system`/`inequality` `solve`, `roots`, `coeff` |
| `Taschenrechner.Series` | Taylor / Maclaurin / Laurent + truncated series arithmetic |
| `Taschenrechner.Limit` | Limits (two-sided/one-sided, poles, `classify`) |
| `Taschenrechner.Sum` | Finite sums (Faulhaber powers 0–6, geometric) |
| `Taschenrechner.ODE` | `dsolve`: 1st-order, 2nd-order const-coeff, systems `Y'=AY` |
| `Taschenrechner.Diff` | `diff`, `diffN`, partials |
| `Taschenrechner.Trig` | Trig preprocess (product-to-sum, power-reduce) + linear integrals |
| `Taschenrechner.Poly` | Univariate polynomials over ℚ |
| `Taschenrechner.RatInt` | Rational integration + `apart` (partial fractions) |
| `Taschenrechner.Risch` | Transcendental Risch (exp/log/trig, non-existence) |
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
2x(x+1)              # juxtaposition = multiply
sin(x^2)
-x^2 + 1             # unary minus; ^ binds tighter → -(x^2)
2+3*i                # complex rationals ℚ(i)
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
| `nf(e)` / `normal(e)` | `simplify` → `cancel` → `together` → `simplify` |

```bash
lake exe taschenrechner 'cancel((x^2-1)/(x-1))'   # → 1 + x
lake exe taschenrechner 'together(1/x + 1/(x+1))' # → (1+2x)/(x+x²)
lake exe taschenrechner 'nf(1/x + 2/x)'           # → 3/x
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

**Factor, solve, systems & inequalities**

| Form | What it does |
|------|----------------|
| `factor(e[, v])` | Factor poly/rational over ℚ; integers → `[prime, exp; …]` matrix |
| `roots(e[, v])` | Roots of `e=0` as a 1×n matrix (rational + quadratic) |
| `solve(f[, x])` | Roots of scalar `f=0`; also `solve(A,b)` for matrices |
| `solve(lhs=rhs[, x])` | Equation form (preferred) |
| `solve(lhs, rhs, x)` | Solve `lhs = rhs` (3-arg form) |
| `solve(eq1, eq2, …[, x, y, …])` | **Linear system** → named eqs `x = …, y = …` (var order explicit or alphabetical) |
| `solve(expr ? 0)` / `solve(a ? b)` | **Inequality** → merged intervals with open/closed ends; print as `(-∞, -1) ∪ [1, ∞)` |
| `collect(e[, v])` | Rewrite as canonical poly/rational in `v` |
| `coeff(e, n)` / `coeff(e, v, n)` | Coefficient of `v^n` |

Relations parse at top level: `a = b`, `a < b`, `a <= b` / `a ≤ b`, `a > b`, `a >= b` / `a ≥ b` (`>`/`≥` normalize to flipped `<`/`≤`). Systems require linear equations; inequalities are univariate polynomial. Internally intervals are n×4 rows `[lo, hi, loClosed, hiClosed]` (CLI pretty-prints unions); whole line → `ℝ`, empty → `∅`, scalar roots → `{…}`.

```bash
lake exe taschenrechner 'factor(x^2-1)'              # → (x-1)(x+1)
lake exe taschenrechner 'solve(x^2=4, x)'             # → {2, -2}
lake exe taschenrechner 'solve(x^2-5*x+6=0, x)'       # → {3, 2}
lake exe taschenrechner 'solve(x^2, 4, x)'            # → {2, -2}  (3-arg form)
lake exe taschenrechner 'solve(x+y=1, x-y=3)'         # → x = 2, y = -1
lake exe taschenrechner 'solve(x+y+z=6, x-y=1, y-z=1)' # → x = 3, y = 2, z = 1
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
| `modal(A)` / `diagform(A)` | Just `P` or just `D` |
| `expm(A)` | `P exp(D) P⁻¹` for diagonalizable `A` |

```bash
lake exe taschenrechner 'charpoly([1, 0; 0, 2])'      # → t² − 3t + 2
lake exe taschenrechner 'eigvals([0, -1; 1, 0])'       # → [-i, i]
lake exe taschenrechner 'eigenspace([1, 0; 0, 2], 2)' # → [0; 1]
lake exe taschenrechner 'diagform([1, 0; 0, 2])'       # → diag(1,2) (order may vary)
lake exe taschenrechner 'expm(zeros(2))'              # → I
```

**Finite sums & ODEs**

| Form | What it does |
|------|----------------|
| `sum(expr, k, lo, hi)` | ∑_{k=lo}^{hi} expr (Faulhaber / geometric; **numeric** if bounds are ints) |
| `sum(k, lo, hi, expr)` | Same, index-first order |
| `dsolve(eq)` | 1st-order (`y'`/`yp`) or 2nd-order const-coeff (`y''`/`ypp`) |
| `dsolve(eq, y, x)` | Specify unknown and independent variable |
| `dsolve(eq, x0, y0)` | IC y(x0)=y0 (first-order) |
| `dsolve(eq, x0, y0, yp0)` | ICs y(x0)=y0, y′(x0)=yp0 (second-order) |
| `dsolve(eq, y, x, x0, y0[, yp0])` | Full IC form |
| `dsolve(A)` | Linear system **Y′ = A Y** → `yᵢ = (Φ(x)·C)ᵢ`, Φ=expm(A x) |
| `dsolve(A, Y0)` | System with Y(0)=Y0 |
| `C` / `C1`,`C2` | Arbitrary constants (fixed by ICs) |

Linear 1st-order: `y' + P(x)*y = Q(x)`. Separable: `y' = f(x)*g(y)`. Const-coeff 2nd-order: `a y'' + b y' + c y = g` (g constant). Systems require diagonalizable A.

```bash
lake exe taschenrechner 'sum(k, 1, n, k)'              # → n(n+1)/2
lake exe taschenrechner 'sum(k, 1, 10, k)'             # → 55
lake exe taschenrechner 'dsolve(y'\'' + y = 0)'         # → y = C·exp(-x)
lake exe taschenrechner 'dsolve(y'\'' + y = x)'         # → y = C·exp(-x) + x − 1
lake exe taschenrechner 'dsolve(yp + y = 0, 0, 1)'     # → y = exp(-x)
lake exe taschenrechner 'dsolve(yp = x*y)'             # → y = C·exp(x²/2)
lake exe taschenrechner "dsolve(y'' + y = 0)"          # → y = C1·cos(x) + C2·sin(x)
lake exe taschenrechner "dsolve(y'' + y = 0, 0, 1, 0)" # → y = cos(x)
lake exe taschenrechner 'dsolve([1,0;0,2])'            # → y1 = C1·exp(x), y2 = C2·exp(2x)
lake exe taschenrechner 'dsolve([1,0;0,2],[3;4])'      # → y1 = 3·exp(x), y2 = 4·exp(2x)
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
2. **Heuristics** (if Risch returns undecided): reverse chain rule for non-linear args, by-parts

**Not fully covered:** algebraic extensions (general radicals / algebraic curves), arbitrary nested towers, special functions beyond elementary.

```bash
lake exe taschenrechner 'int 1/(x^2+1)'   # atan(x)
lake exe taschenrechner 'int exp(x^2)'     # not elementary (Risch)
lake exe taschenrechner 'int x*exp(x^2)'   # 1/2·exp(x^2)
```
