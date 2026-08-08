# Taschenrechner

A small **computer algebra system** written in [Lean 4](https://lean-lang.org/), supporting:

- Symbolic expression trees with exact rational coefficients  
- Algebraic simplification and expansion  
- Symbolic differentiation (product, chain, power, elementary functions)  
- Symbolic indefinite & definite integration (table lookup, power rule, reverse chain rule, linear composites, integration by parts)

## Build & run

```bash
lake build
lake exe taschenrechner                 # demo
lake exe taschenrechner 'x^2 + 2x + 1'  # parse & print
lake exe taschenrechner 'diff sin(x^2)'
lake exe taschenrechner 'int x*exp(x)'
lake exe taschenrechner -i              # REPL
lake exe taschenrechner --help          # language help
lake exe taschenrechner --regression    # 40-case integration suite
```

Compile-time guard tests live in `Taschenrechner/Tests.lean` (built with the library).

## Library overview

| Module | Role |
|--------|------|
| `Taschenrechner.Expr` | AST (`Expr`), rationals (`RatConst`), pretty-printing |
| `Taschenrechner.Simplify` | Constant folding, like-term collection, expand |
| `Taschenrechner.Diff` | `diff`, `diffN`, partials |
| `Taschenrechner.Trig` | Trig preprocess (product-to-sum, power-reduce) + linear integrals |
| `Taschenrechner.Poly` | Univariate polynomials over ℚ |
| `Taschenrechner.RatInt` | Rational function integration (Hermite + Rothstein–Trager) |
| `Taschenrechner.Risch` | Transcendental Risch (exp/log/trig, non-existence) |
| `Taschenrechner.Integrate` | Structured `IntegrateResult`, verified `integrate` |
| `Taschenrechner.Parse` | Lexer + recursive-descent parser (`parse`, `parseCommand`) |
| `Taschenrechner.Regression` | 40-case integration regression suite |

## Expression language

```
x^2 + 3*x + 1
2x(x+1)              # juxtaposition = multiply
sin(x^2)
-x^2 + 1             # unary minus; ^ binds tighter → -(x^2)
diff(sin(x^2), x)    # CAS forms inside expressions
int(x*exp(x))
```

Commands: `diff <expr> [var]`, `int <expr> [var]`, `simplify <expr>`, `expand <expr>`, `help`.

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
   - **Non-existence certificates**, e.g. `∫ exp(x²) dx` is not elementary; `∫ x·exp(x²) dx = ½ exp(x²)` is
   - Simple log patterns (`ln(x)^n / x`, `ln(x)^n`)
2. **Heuristics** (if Risch returns undecided): reverse chain rule for non-linear args, by-parts

**Not fully covered:** algebraic extensions (general radicals / algebraic curves), arbitrary nested towers, special functions beyond elementary.

```bash
lake exe taschenrechner 'int 1/(x^2+1)'   # atan(x)
lake exe taschenrechner 'int exp(x^2)'     # not elementary (Risch)
lake exe taschenrechner 'int x*exp(x^2)'   # 1/2·exp(x^2)
```
