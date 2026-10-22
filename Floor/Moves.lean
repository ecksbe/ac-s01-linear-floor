import AC
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Floor.Moves — the 14 move codes (ac-r2-v1) on ordered pairs, and their soundness

`Pair` is an ordered pair (r0, r1) of words in the free group on x = `of 0`, y = `of 1`.
`apply m` is move code `m` as listed in the official `move_spec.json`:

* c0: r0 ← r0⁻¹, c1: r1 ← r1⁻¹;
* c2: r0 ← r0 r1, c3: r0 ← r0 r1⁻¹, c4: r1 ← r1 r0, c5: r1 ← r1 r0⁻¹;
* c6..c9: r0 ← g r0 g⁻¹ for g = x, x⁻¹, y, y⁻¹; c10..c13: the same on r1.

Words are elements of `FreeGroup`, so free reduction is built in. `apply_sound` shows that every
code is a finite sequence of official `AC.Step`s on `toRel p`. Codes 3 and 5 use three steps
(invert the other relator, multiply, restore).
-/

namespace Floor

open AC

/-- Words on the two generators. -/
abbrev F2 := FreeGroup (Fin 2)

/-- An ordered pair of relators. -/
abbrev Pair := F2 × F2

/-- The generator x. -/
def gx : F2 := FreeGroup.of 0

/-- The generator y. -/
def gy : F2 := FreeGroup.of 1

/-- A letter: a generator with a sign (`true` for the generator, `false` for its inverse). -/
abbrev Letter := Fin 2 × Bool

/-- The standard pair (x, y). -/
def standard : Pair := (gx, gy)

/-- The 14 move codes of `move_spec.json`, in order. -/
inductive Move
  | c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13
  deriving DecidableEq, Repr

namespace Move

/-- The numeric code of a move. -/
def code : Move → ℕ
  | c0 => 0 | c1 => 1 | c2 => 2 | c3 => 3 | c4 => 4 | c5 => 5 | c6 => 6
  | c7 => 7 | c8 => 8 | c9 => 9 | c10 => 10 | c11 => 11 | c12 => 12 | c13 => 13

/-- Codes 6–13: conjugation of one relator by one generator letter. -/
def IsConj (m : Move) : Prop := 6 ≤ m.code

instance (m : Move) : Decidable m.IsConj := inferInstanceAs (Decidable (6 ≤ m.code))

end Move

open Move

/-- The action of one move code on a pair. -/
def apply : Move → Pair → Pair
  | c0, p => (p.1⁻¹, p.2)
  | c1, p => (p.1, p.2⁻¹)
  | c2, p => (p.1 * p.2, p.2)
  | c3, p => (p.1 * p.2⁻¹, p.2)
  | c4, p => (p.1, p.2 * p.1)
  | c5, p => (p.1, p.2 * p.1⁻¹)
  | c6, p => (gx * p.1 * gx⁻¹, p.2)
  | c7, p => (gx⁻¹ * p.1 * gx, p.2)
  | c8, p => (gy * p.1 * gy⁻¹, p.2)
  | c9, p => (gy⁻¹ * p.1 * gy, p.2)
  | c10, p => (p.1, gx * p.2 * gx⁻¹)
  | c11, p => (p.1, gx⁻¹ * p.2 * gx)
  | c12, p => (p.1, gy * p.2 * gy⁻¹)
  | c13, p => (p.1, gy⁻¹ * p.2 * gy)

/-- Apply a list of moves, first move first. -/
def applyList : List Move → Pair → Pair
  | [], p => p
  | m :: ms, p => applyList ms (apply m p)

/-- The number of conjugation moves (codes 6–13). -/
def conjCount (ms : List Move) : ℕ := (ms.filter (fun m => decide m.IsConj)).length

/-- The number of non-conjugation moves (codes 0–5). -/
def nonconjCount (ms : List Move) : ℕ := (ms.filter (fun m => !decide m.IsConj)).length

@[simp] theorem applyList_nil (p : Pair) : applyList [] p = p := rfl

@[simp] theorem applyList_cons (m : Move) (ms : List Move) (p : Pair) :
    applyList (m :: ms) p = applyList ms (apply m p) := rfl

/-- Every move is either a conjugation or not: the two counts add up to the length. -/
theorem length_eq_counts (ms : List Move) :
    ms.length = conjCount ms + nonconjCount ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    unfold conjCount nonconjCount at *
    by_cases h : m.IsConj <;> simp [h, ih] <;> omega

/-! ### The bridge to the official relator type -/

/-- A pair as official rank-2 relators. -/
def toRel (p : Pair) : Relators 2 := ![p.1, p.2]

@[simp] theorem toRel_zero (p : Pair) : toRel p 0 = p.1 := rfl

@[simp] theorem toRel_one (p : Pair) : toRel p 1 = p.2 := rfl

theorem toRel_standard : toRel standard = AC.standard 2 := by
  funext i
  fin_cases i <;> rfl

theorem update_zero (p : Pair) (w : F2) : Function.update (toRel p) 0 w = toRel (w, p.2) := by
  funext i
  fin_cases i <;> rfl

theorem update_one (p : Pair) (w : F2) : Function.update (toRel p) 1 w = toRel (p.1, w) := by
  funext i
  fin_cases i <;> rfl

theorem reach_inv0 (p : Pair) : Reachable (toRel p) (toRel (p.1⁻¹, p.2)) := by
  have h := Step.inv (toRel p) 0
  rw [update_zero] at h
  exact Relation.ReflTransGen.single h

theorem reach_inv1 (p : Pair) : Reachable (toRel p) (toRel (p.1, p.2⁻¹)) := by
  have h := Step.inv (toRel p) 1
  rw [update_one] at h
  exact Relation.ReflTransGen.single h

theorem reach_mul01 (p : Pair) : Reachable (toRel p) (toRel (p.1 * p.2, p.2)) := by
  have h := Step.mulRight (toRel p) 0 1 (by decide)
  rw [update_zero] at h
  exact Relation.ReflTransGen.single h

theorem reach_mul10 (p : Pair) : Reachable (toRel p) (toRel (p.1, p.2 * p.1)) := by
  have h := Step.mulRight (toRel p) 1 0 (by decide)
  rw [update_one] at h
  exact Relation.ReflTransGen.single h

theorem reach_conj0 (p : Pair) (w : F2) : Reachable (toRel p) (toRel (w * p.1 * w⁻¹, p.2)) := by
  have h := Step.conj (toRel p) 0 w
  rw [update_zero] at h
  exact Relation.ReflTransGen.single h

theorem reach_conj1 (p : Pair) (w : F2) : Reachable (toRel p) (toRel (p.1, w * p.2 * w⁻¹)) := by
  have h := Step.conj (toRel p) 1 w
  rw [update_one] at h
  exact Relation.ReflTransGen.single h

/-- Code 3 as three official steps: invert r1, multiply r0 by it, invert r1 back. -/
theorem reach_mulinv01 (p : Pair) : Reachable (toRel p) (toRel (p.1 * p.2⁻¹, p.2)) := by
  have h1 := reach_inv1 p
  have h2 := reach_mul01 (p.1, p.2⁻¹)
  have h3 := reach_inv1 (p.1 * p.2⁻¹, p.2⁻¹)
  simp only [inv_inv] at h3
  exact (h1.trans h2).trans h3

/-- Code 5 as three official steps: invert r0, multiply r1 by it, invert r0 back. -/
theorem reach_mulinv10 (p : Pair) : Reachable (toRel p) (toRel (p.1, p.2 * p.1⁻¹)) := by
  have h1 := reach_inv0 p
  have h2 := reach_mul10 (p.1⁻¹, p.2)
  have h3 := reach_inv0 (p.1⁻¹, p.2 * p.1⁻¹)
  simp only [inv_inv] at h3
  exact (h1.trans h2).trans h3

/-- **Soundness.** Every move code is a finite sequence of official AC steps. -/
theorem apply_sound (m : Move) (p : Pair) : Reachable (toRel p) (toRel (apply m p)) := by
  cases m
  · exact reach_inv0 p
  · exact reach_inv1 p
  · exact reach_mul01 p
  · exact reach_mulinv01 p
  · exact reach_mul10 p
  · exact reach_mulinv10 p
  · exact reach_conj0 p gx
  · simpa using reach_conj0 p gx⁻¹
  · exact reach_conj0 p gy
  · simpa using reach_conj0 p gy⁻¹
  · exact reach_conj1 p gx
  · simpa using reach_conj1 p gx⁻¹
  · exact reach_conj1 p gy
  · simpa using reach_conj1 p gy⁻¹

/-- A list of move codes is a finite sequence of official AC steps. -/
theorem applyList_sound (ms : List Move) (p : Pair) :
    Reachable (toRel p) (toRel (applyList ms p)) := by
  induction ms generalizing p with
  | nil => exact Relation.ReflTransGen.refl
  | cons m ms ih => exact (apply_sound m p).trans (ih (apply m p))

end Floor
