/-
  Unicode math symbols for the CLI: catalog, lookup, and identifier rules
  so Greek / ∞ / operators can appear in expressions and assignments.
-/
namespace Taschenrechner

/-- How a picked glyph is inserted into the next statement. -/
inductive UniInsert where
  /-- Prefix the glyph (`√`, `π`, `∫`, Greek). -/
  | prefix
  /-- Infix / relation: user types a full expression (`×`, `≤`). -/
  | infix
  deriving Repr, BEq, Inhabited

structure UniSym where
  glyph    : String
  names    : List String
  cat      : String
  meaning  : String
  insert   : UniInsert := .prefix
  deriving Repr, Inhabited

def uniCatalog : Array UniSym := #[
  -- operators
  { glyph := "−", names := ["minus", "sub"], cat := "operators",
    meaning := "minus", insert := .infix },
  { glyph := "×", names := ["times", "mul", "cross"], cat := "operators",
    meaning := "multiply", insert := .infix },
  { glyph := "÷", names := ["div", "divide"], cat := "operators",
    meaning := "divide", insert := .infix },
  { glyph := "·", names := ["cdot", "dot"], cat := "operators",
    meaning := "multiply", insert := .infix },
  { glyph := "√", names := ["sqrt", "root"], cat := "operators",
    meaning := "square root" },
  { glyph := "^", names := ["pow", "caret", "power"], cat := "operators",
    meaning := "power", insert := .infix },
  -- relations
  { glyph := "≠", names := ["ne", "neq", "notequal"], cat := "relations",
    meaning := "not equal", insert := .infix },
  { glyph := "≤", names := ["le", "leq", "leeq"], cat := "relations",
    meaning := "less or equal", insert := .infix },
  { glyph := "≥", names := ["ge", "geq", "geeq"], cat := "relations",
    meaning := "greater or equal", insert := .infix },
  { glyph := "≈", names := ["approx", "asymp"], cat := "relations",
    meaning := "approximately equal", insert := .infix },
  { glyph := "≡", names := ["equiv", "eqeq"], cat := "relations",
    meaning := "identical / equal", insert := .infix },
  -- calculus
  { glyph := "∫", names := ["int", "integral"], cat := "calculus",
    meaning := "integral  int(f) / int(f,x)" },
  { glyph := "∑", names := ["sum", "sigma"], cat := "calculus",
    meaning := "sum  sum(expr,k,lo,hi)" },
  { glyph := "∏", names := ["prod", "product"], cat := "calculus",
    meaning := "product  product(expr,k,lo,hi)" },
  { glyph := "∂", names := ["partial", "diff", "del"], cat := "calculus",
    meaning := "derivative  diff(f) / diff(f,x)" },
  { glyph := "∞", names := ["inf", "oo", "infty", "infinity"], cat := "calculus",
    meaning := "infinity" },
  -- constants
  { glyph := "π", names := ["pi"], cat := "constants",
    meaning := "pi" },
  -- greek (variables, plus π already listed)
  { glyph := "α", names := ["alpha"], cat := "greek", meaning := "alpha" },
  { glyph := "β", names := ["beta"], cat := "greek", meaning := "beta" },
  { glyph := "γ", names := ["gamma"], cat := "greek", meaning := "gamma" },
  { glyph := "δ", names := ["delta"], cat := "greek", meaning := "delta" },
  { glyph := "ε", names := ["epsilon", "eps"], cat := "greek", meaning := "epsilon" },
  { glyph := "θ", names := ["theta"], cat := "greek", meaning := "theta" },
  { glyph := "λ", names := ["lambda"], cat := "greek", meaning := "lambda" },
  { glyph := "μ", names := ["mu"], cat := "greek", meaning := "mu" },
  { glyph := "ξ", names := ["xi"], cat := "greek", meaning := "xi" },
  { glyph := "ρ", names := ["rho"], cat := "greek", meaning := "rho" },
  { glyph := "σ", names := ["sigma"], cat := "greek", meaning := "sigma" },
  { glyph := "φ", names := ["phi"], cat := "greek", meaning := "phi" },
  { glyph := "ψ", names := ["psi"], cat := "greek", meaning := "psi" },
  { glyph := "ω", names := ["omega"], cat := "greek", meaning := "omega" },
  { glyph := "Γ", names := ["Gamma"], cat := "greek", meaning := "Gamma" },
  { glyph := "Δ", names := ["Delta"], cat := "greek", meaning := "Delta" },
  { glyph := "Θ", names := ["Theta"], cat := "greek", meaning := "Theta" },
  { glyph := "Λ", names := ["Lambda"], cat := "greek", meaning := "Lambda" },
  { glyph := "Σ", names := ["Sigma"], cat := "greek", meaning := "Sigma" },
  { glyph := "Φ", names := ["Phi"], cat := "greek", meaning := "Phi" },
  { glyph := "Ω", names := ["Omega"], cat := "greek", meaning := "Omega" }
]

/-- 1-based index into `uniCatalog`. -/
def uniByIndex? (n : Nat) : Option UniSym :=
  if n == 0 then none
  else uniCatalog[n - 1]?

def uniByName? (q : String) : Option UniSym :=
  let ql := q.toLower
  uniCatalog.find? fun s =>
    s.glyph == q || s.names.any (fun n => n.toLower == ql)

/-- Number, alias, or the glyph itself. -/
def uniLookup? (q : String) : Option UniSym :=
  match q.toNat? with
  | some n => uniByIndex? n
  | none => uniByName? q

def uniCategories : List String :=
  ["operators", "relations", "calculus", "constants", "greek"]

def formatUniGroup (cat : String) : String :=
  let items :=
    Id.run do
      let mut parts : List String := []
      for i in [:uniCatalog.size] do
        let s := uniCatalog[i]!
        if s.cat == cat then
          let alias := s.names.headD ""
          parts := parts ++ [s!"{i + 1} {s.glyph}  {alias}"]
      pure parts
  if items.isEmpty then ""
  else s!"  {cat}\n    " ++ String.intercalate "   " items

def formatUniCatalog : String :=
  let body :=
    uniCategories.foldl (fun acc c =>
      let g := formatUniGroup c
      if g.isEmpty then acc
      else if acc.isEmpty then g else acc ++ "\n" ++ g) ""
  "Unicode symbols  (number or name; then an expression)\n" ++ body ++
    "\n  pick>  number/name   expr>  rest of statement  (q cancels)"

def formatUniSym (s : UniSym) : String :=
  let als := String.intercalate ", " s.names
  s!"  {s.glyph}    {als}    {s.meaning}"

/-- Greek and Coptic block, plus a few letter-like math symbols. -/
def isGreekLetter (c : Char) : Bool :=
  let n := c.toNat
  (0x0370 ≤ n && n ≤ 0x03FF) || (0x1F00 ≤ n && n ≤ 0x1FFF)

def isUnicodeIdentStart (c : Char) : Bool :=
  isGreekLetter c || c == '∞' || c == '∅'

def isUnicodeIdentCont (c : Char) : Bool :=
  isUnicodeIdentStart c

end Taschenrechner
