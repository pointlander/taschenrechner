/-
  Unicode identifier rules so Greek letters, ∞, and ∅ can appear
  in expressions and assignment names.
-/
namespace Taschenrechner

/-- Greek and Coptic block, plus extended Greek. -/
def isGreekLetter (c : Char) : Bool :=
  let n := c.toNat
  (0x0370 ≤ n && n ≤ 0x03FF) || (0x1F00 ≤ n && n ≤ 0x1FFF)

def isUnicodeIdentStart (c : Char) : Bool :=
  isGreekLetter c || c == '∞' || c == '∅'

def isUnicodeIdentCont (c : Char) : Bool :=
  isUnicodeIdentStart c

end Taschenrechner
