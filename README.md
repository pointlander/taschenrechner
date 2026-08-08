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
```

Compile-time guard tests live in `Taschenrechner/Tests.lean` (built with the library).

## Library overview

| Module | Role |
|--------|------|
| `Taschenrechner.Expr` | AST (`Expr`), rationals (`RatConst`), pretty-printing |
| `Taschenrechner.Simplify` | Constant folding, like-term collection, expand |
| `Taschenrechner.Diff` | `diff`, `diffN`, partials |
| `Taschenrechner.Integrate` | `integrate`, `integrateDefinite`, self-check |
| `Taschenrechner.Parse` | Lexer + recursive-descent parser (`parse`, `parseCommand`) |

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

**Differentiation:** constants, polynomials, `sin`/`cos`/`tan`, `exp`, `ln`, products, quotients (as `a·b⁻¹`), general powers.

**Integration:** polynomials & `xⁿ` (including `1/x → ln x`), linear combinations, `sin`/`cos`/`tan`/`exp`/`ln` of linear arguments, reverse chain-rule patterns (`f'(g)·g'`), simple integration by parts (`x·exp(x)`, `x·ln(x)`, …).

Not a full Risch implementation: many special functions and algebraic integrals will return `.failure`.
