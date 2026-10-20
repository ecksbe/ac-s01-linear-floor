import Floor.Moves
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Floor.S01 — the symbolic pairs S01(n) and their match with the official text

`S01 n = (P, Q n)` with `P = y⁻¹ x⁻¹ y x⁻¹ y x` and `Q n = y⁻ⁿ x⁻¹ y^(n-1) x`, the exponents
read in ℤ (so `Q n` is defined for every `n`).

The official puzzle text writes each relator letter by letter (`y^-1 y^-1 ...`). `parseDesc` reads
such a text into a pair (a small structural parser on the character list), and `official_eq`
checks by `decide` (kernel reduction, no native code) that the official lines for n = 4..11 parse
to exactly `S01 n`.
-/

namespace Floor

/-- The first relator `y⁻¹ x⁻¹ y x⁻¹ y x`. -/
def P : F2 := gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx

/-- The second relator `y⁻ⁿ x⁻¹ y^(n-1) x`. -/
def Q (n : ℕ) : F2 := gy ^ (-(n : ℤ)) * gx⁻¹ * gy ^ ((n : ℤ) - 1) * gx

/-- The symbolic start pair. -/
def S01 (n : ℕ) : Pair := (P, Q n)

/-! ### Reading the official text -/

/-- Split a character list at spaces. -/
def splitSp : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = ' ' then [] :: splitSp cs
    else
      match splitSp cs with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

/-- One letter token: `x`, `x^-1`, `y` or `y^-1`. -/
def tok : List Char → Option Letter
  | ['x'] => some (0, true)
  | ['x', '^', '-', '1'] => some (0, false)
  | ['y'] => some (1, true)
  | ['y', '^', '-', '1'] => some (1, false)
  | _ => none

/-- Letter tokens up to the token `=`, and the tokens after it. -/
def letters : List (List Char) → Option (List Letter × List (List Char))
  | [] => none
  | t :: ts =>
    if t = ['='] then some ([], ts)
    else
      match tok t, letters ts with
      | some l, some (ls, rest) => some (l :: ls, rest)
      | _, _ => none

/-- Parse `Presentation: <x, y | r0 = 1; r1 = 1>.` into a pair. -/
def parseDesc (s : String) : Option Pair :=
  match splitSp s.toList with
  | p :: g :: h :: b :: ts =>
    if p = "Presentation:".toList ∧ g = "<x,".toList ∧ h = ['y'] ∧ b = ['|'] then
      match letters ts with
      | some (l0, s1 :: ts') =>
        if s1 = "1;".toList then
          match letters ts' with
          | some (l1, [e]) =>
            if e = "1>.".toList then some (FreeGroup.mk l0, FreeGroup.mk l1) else none
          | _ => none
        else none
      | _ => none
    else none
  | _ => none

/-! ### The official lines, n = 4..11 (description text copied unedited) -/

theorem official_eq_4 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 x^-1 y y y x = 1>."
    = some (S01 4) := by decide

theorem official_eq_5 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y x = 1>."
    = some (S01 5) := by decide

theorem official_eq_6 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y x = 1>."
    = some (S01 6) := by decide

theorem official_eq_7 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y y x = 1>."
    = some (S01 7) := by decide

theorem official_eq_8 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y y y x = 1>."
    = some (S01 8) := by decide

set_option maxRecDepth 8000 in
theorem official_eq_9 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y y y y x = 1>."
    = some (S01 9) := by decide

set_option maxRecDepth 8000 in
theorem official_eq_10 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y y y y y x = 1>."
    = some (S01 10) := by decide

set_option maxRecDepth 8000 in
theorem official_eq_11 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y y y y y y x = 1>."
    = some (S01 11) := by decide

/-- The parser is not vacuous: the n = 6 text does not parse to `S01 5` or `S01 7`. -/
theorem official_ne_6 : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y x = 1>."
    ≠ some (S01 5) ∧ parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y x = 1>."
    ≠ some (S01 7) := by decide

/-- The official relators for n = 4, as `AC.Relators 2`. -/
theorem toRel_official_4 {R : Pair} (h : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 x^-1 y y y x = 1>."
    = some R) : toRel (S01 4) = toRel R := by
  rw [official_eq_4] at h
  cases h; rfl

/-- The official relators for n = 6, as `AC.Relators 2`. -/
theorem toRel_official_6 {R : Pair} (h : parseDesc
    "Presentation: <x, y | y^-1 x^-1 y x^-1 y x = 1; y^-1 y^-1 y^-1 y^-1 y^-1 y^-1 x^-1 y y y y y x = 1>."
    = some R) : toRel (S01 6) = toRel R := by
  rw [official_eq_6] at h
  cases h; rfl

end Floor
