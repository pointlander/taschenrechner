/-
  Multi-line ASCII-art pretty-printer for expressions.

  Layout is a rectangular box with a baseline row so fractions, powers,
  and side-by-side operators align like textbook notation:

        2
       x  + 1
      ─────────
         x
-/
import Taschenrechner.Expr
import Taschenrechner.Matrix

namespace Taschenrechner

open Expr

/-- Rectangular glyph box with a baseline (row of the main line). -/
structure Box where
  lines    : Array String
  width    : Nat
  height   : Nat
  baseline : Nat
  deriving Repr, Inhabited

namespace Box

def empty : Box := ⟨#[], 0, 0, 0⟩

def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

def padTo (s : String) (w : Nat) : String :=
  if s.length ≥ w then s
  else s ++ spaces (w - s.length)

def text (s : String) : Box :=
  let s := if s.contains '\n' then s.replace "\n" " " else s
  ⟨#[s], s.length, 1, 0⟩

def normalize (b : Box) : Box :=
  if b.height == 0 then empty
  else
    { b with lines := b.lines.map fun s => padTo s b.width }

/-- Horizontal concat with baseline alignment. -/
def hcat (a b : Box) (gap : Nat := 0) : Box :=
  let a := normalize a; let b := normalize b
  if a.height == 0 then b
  else if b.height == 0 then a
  else
    let above := max a.baseline b.baseline
    let below := max (a.height - 1 - a.baseline) (b.height - 1 - b.baseline)
    let h := above + 1 + below
    let gapS := spaces gap
    let w := a.width + gap + b.width
    Id.run do
      let mut lines : Array String := Array.empty
      for i in [:h] do
        let rowA := (i : Int) + a.baseline - above
        let rowB := (i : Int) + b.baseline - above
        let sa :=
          if rowA ≥ 0 && rowA < a.height then a.lines[rowA.toNat]!
          else spaces a.width
        let sb :=
          if rowB ≥ 0 && rowB < b.height then b.lines[rowB.toNat]!
          else spaces b.width
        lines := lines.push (sa ++ gapS ++ sb)
      pure ⟨lines, w, h, above⟩

/-- Fraction num/den with a bar; baseline on the bar. -/
def fraction (num den : Box) : Box :=
  let num := normalize num; let den := normalize den
  let w := max num.width den.width + 2
  let center (b : Box) : Array String :=
    b.lines.map fun s =>
      let pad := (w - s.length) / 2
      spaces pad ++ s ++ spaces (w - s.length - pad)
  let bar := String.ofList (List.replicate w '─')
  let lines := (center num).push bar ++ center den
  let h := num.height + 1 + den.height
  ⟨lines, w, h, num.height⟩

/-- Multi-line parentheses (ASCII). -/
def paren (b : Box) : Box :=
  let b := normalize b
  if b.height ≤ 1 then
    text s!"({if b.height == 1 then b.lines[0]! else ""})"
  else
    Id.run do
      let mut lines : Array String := Array.empty
      for i in [:b.height] do
        let l := if i == 0 then "/" else if i + 1 == b.height then "\\" else "|"
        let r := if i == 0 then "\\" else if i + 1 == b.height then "/" else "|"
        lines := lines.push (l ++ b.lines[i]! ++ r)
      pure ⟨lines, b.width + 2, b.height, b.baseline⟩

/-- Place exp above-right of base. -/
def power (base exp : Box) : Box :=
  let base := normalize base; let exp := normalize exp
  let above := exp.height
  let h := above + base.height
  let w := base.width + exp.width
  Id.run do
    let mut lines : Array String := Array.empty
    for i in [:above] do
      lines := lines.push (spaces base.width ++ exp.lines[i]!)
    for i in [:base.height] do
      lines := lines.push (base.lines[i]! ++ spaces exp.width)
    pure ⟨lines, w, h, above + base.baseline⟩

def funcCall (name : String) (arg : Box) : Box :=
  let arg := normalize arg
  if arg.height ≤ 1 then
    text s!"{name}({if arg.height == 1 then arg.lines[0]! else ""})"
  else
    hcat (text name) (paren arg) 0

def render (b : Box) : String :=
  let b := normalize b
  if b.lines.isEmpty then ""
  else String.intercalate "\n" b.lines.toList

end Box

/-! ### Expression → Box -/

def needsParenMul : Expr → Bool
  | add _ _ | eq _ _ | lt _ _ | le _ _ => true
  | _ => false

def needsParenPow : Expr → Bool
  | add _ _ | mul _ _ | pow _ _ | eq _ _ | lt _ _ | le _ _ => true
  | _ => false

partial def asFrac? : Expr → Option (Expr × Expr)
  | mul a (pow b (const r)) =>
    match CplxConst.toRat? r with
    | some q => if q == RatConst.negOne then some (a, b) else none
    | none => none
  | mul (pow b (const r)) a =>
    match CplxConst.toRat? r with
    | some q => if q == RatConst.negOne then some (a, b) else none
    | none => none
  | _ => none

def asInv? : Expr → Option Expr
  | pow b (const r) =>
    match CplxConst.toRat? r with
    | some q => if q == RatConst.negOne then some b else none
    | none => none
  | _ => none

def supNat : Nat → String
  | 0 => "⁰" | 1 => "¹" | 2 => "²" | 3 => "³" | 4 => "⁴"
  | 5 => "⁵" | 6 => "⁶" | 7 => "⁷" | 8 => "⁸" | 9 => "⁹"
  | n => s!"^{n}"

partial def exprToBox (e : Expr) : Box :=
  match e with
  | const c => Box.text (CplxConst.toString c)
  | var v => Box.text (if isInfName v then "∞" else v)
  | add a b => sumToBox (flattenAddLocal (add a b))
  | mul a b =>
    match asFrac? (mul a b) with
    | some (num, den) =>
      -- Pull leading minus outside the fraction when possible
      match num with
      | mul (const r) rest =>
        if r.isNegOne then
          Box.hcat (Box.text "-") (Box.fraction (exprToBox rest) (exprToBox den)) 0
        else
          Box.fraction (exprToBox num) (exprToBox den)
      | const r =>
        if r.isReal && r.re.num < 0 then
          Box.hcat (Box.text "-")
            (Box.fraction (Box.text (CplxConst.toString (CplxConst.neg r)))
              (exprToBox den)) 0
        else
          Box.fraction (exprToBox num) (exprToBox den)
      | _ => Box.fraction (exprToBox num) (exprToBox den)
    | none => productToBox (mul a b)
  | pow a b =>
    match asInv? (pow a b) with
    | some den => Box.fraction (Box.text "1") (exprToBox den)
    | none =>
      let bb :=
        if needsParenPow a then Box.paren (exprToBox a) else exprToBox a
      match b with
      | const r =>
        match CplxConst.toRat? r with
        | some q =>
          if q.den == 1 && q.num ≥ 0 && q.num ≤ 9 && bb.height == 1 then
            Box.text (bb.lines[0]! ++ supNat q.num.toNat)
          else if q == ⟨1, 2⟩ then
            Box.hcat (Box.text "√") (Box.paren (exprToBox a)) 0
          else
            Box.power bb (exprToBox b)
        | none => Box.power bb (exprToBox b)
      | _ => Box.power bb (exprToBox b)
  | sin a => Box.funcCall "sin" (exprToBox a)
  | cos a => Box.funcCall "cos" (exprToBox a)
  | tan a => Box.funcCall "tan" (exprToBox a)
  | sinh a => Box.funcCall "sinh" (exprToBox a)
  | cosh a => Box.funcCall "cosh" (exprToBox a)
  | tanh a => Box.funcCall "tanh" (exprToBox a)
  | exp a => Box.funcCall "exp" (exprToBox a)
  | ln a => Box.funcCall "ln" (exprToBox a)
  | atan a => Box.funcCall "atan" (exprToBox a)
  | asin a => Box.funcCall "asin" (exprToBox a)
  | acos a => Box.funcCall "acos" (exprToBox a)
  | abs a =>
    let inner := exprToBox a
    if inner.height == 1 then Box.text s!"|{inner.lines[0]!}|"
    else Box.hcat (Box.hcat (Box.text "|") inner 0) (Box.text "|") 0
  | re a => Box.funcCall "re" (exprToBox a)
  | im a => Box.funcCall "im" (exprToBox a)
  | conj a => Box.funcCall "conj" (exprToBox a)
  | eq a b =>
    Box.hcat (exprToBox a) (Box.hcat (Box.text " = ") (exprToBox b) 0) 0
  | lt a b =>
    Box.hcat (exprToBox a) (Box.hcat (Box.text " < ") (exprToBox b) 0) 0
  | le a b =>
    Box.hcat (exprToBox a) (Box.hcat (Box.text " ≤ ") (exprToBox b) 0) 0
  | mat rows => matToBox rows

where
  sumToBox (terms : List Expr) : Box :=
    match terms with
    | [] => Box.text "0"
    | t :: ts =>
      Id.run do
        let mut acc := signedTerm true t
        for u in ts do
          acc := Box.hcat acc (signedTerm false u) 0
        pure acc

  signedTerm (first : Bool) (t : Expr) : Box :=
    match t with
    | mul (const r) rest =>
      if r.isNegOne then
        let body :=
          if needsParenMul rest then Box.paren (exprToBox rest)
          else exprToBox rest
        if first then Box.hcat (Box.text "-") body 0
        else Box.hcat (Box.text " - ") body 0
      else if r.isReal && r.re.num < 0 then
        let body := exprToBox (mul (const (CplxConst.neg r)) rest)
        if first then Box.hcat (Box.text "-") body 0
        else Box.hcat (Box.text " - ") body 0
      else if first then exprToBox t
      else Box.hcat (Box.text " + ") (exprToBox t) 0
    | const r =>
      if r.isReal && r.re.num < 0 then
        let s := CplxConst.toString (CplxConst.neg r)
        if first then Box.text s!"-{s}" else Box.text s!" - {s}"
      else if first then exprToBox t
      else Box.hcat (Box.text " + ") (exprToBox t) 0
    | _ =>
      if first then exprToBox t
      else Box.hcat (Box.text " + ") (exprToBox t) 0

  productToBox (e : Expr) : Box :=
    let (coeff, nums, dens) := splitProduct e
    if dens.isEmpty then
      let head : List Box :=
        if coeff.isNegOne then [Box.text "-"]
        else if !coeff.isOne && !coeff.isZero then
          [Box.text (CplxConst.toString coeff)]
        else []
      let body := nums.map fun p =>
        if needsParenMul p then Box.paren (exprToBox p) else exprToBox p
      match head ++ body with
      | [] => Box.text (if coeff.isZero then "0" else "1")
      | b :: bs =>
        bs.foldl (fun acc x => Box.hcat (Box.hcat acc (Box.text "·") 0) x 0) b
    else
      let numBody : Expr :=
        match nums with
        | [] =>
          if coeff.isOne || coeff.isNegOne then one
          else const (if coeff.isReal && coeff.re.num < 0 then CplxConst.neg coeff else coeff)
        | p :: ps =>
          let body := ps.foldl mul p
          if coeff.isOne || coeff.isNegOne then body
          else if coeff.isReal && coeff.re.num < 0 then
            mul (const (CplxConst.neg coeff)) body
          else mul (const coeff) body
      let denBody : Expr :=
        match dens with
        | [] => one
        | p :: ps => ps.foldl mul p
      let frac := Box.fraction (exprToBox numBody) (exprToBox denBody)
      if coeff.isNegOne || (coeff.isReal && coeff.re.num < 0) then
        Box.hcat (Box.text "-") frac 0
      else frac

  matToBox (rows : Array (Array Expr)) : Box :=
    if rows.isEmpty then Box.text "[]"
    else
      let cellBoxes := rows.map fun row => row.map exprToBox
      let nR := cellBoxes.size
      let nC := if nR == 0 then 0 else cellBoxes[0]!.size
      let colW : Array Nat :=
        Id.run do
          let mut ws := Array.replicate nC 0
          for row in cellBoxes do
            for j in [:min nC row.size] do
              ws := ws.set! j (max ws[j]! row[j]!.width)
          pure ws
      let rowH := cellBoxes.map fun row =>
        row.foldl (fun m b => max m b.height) 1
      Id.run do
        let mut allLines : Array String := Array.empty
        for i in [:nR] do
          let h := rowH[i]!
          let row := cellBoxes[i]!
          for r in [:h] do
            let mut line := "│"
            for j in [:nC] do
              let b := if j < row.size then Box.normalize row[j]! else Box.text ""
              let w := colW[j]!
              let content :=
                if r < b.height then Box.padTo b.lines[r]! w
                else Box.spaces w
              line := line ++ " " ++ content ++ " "
            line := line ++ "│"
            allLines := allLines.push line
        let w := if allLines.isEmpty then 0 else allLines[0]!.length
        pure ⟨allLines, w, allLines.size, allLines.size / 2⟩

/-- Multi-line ASCII art for an expression. -/
def asciiArt (e : Expr) : String :=
  Box.render (exprToBox e)

end Taschenrechner
