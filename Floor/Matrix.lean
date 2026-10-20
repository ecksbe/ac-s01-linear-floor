import Floor.S01
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Floor.Matrix — exponent-sum rows and the three forced non-conjugation moves

`e w ∈ ℤ × ℤ` is the (x-sum, y-sum) of a word, and `expQ p = (e p.1, e p.2)` its two rows.
Codes 0–5 act on the rows by one elementary row operation (`rowAct`); codes 6–13 fix them.

`three_nonconj`: every route from `S01 n` to (x, y) has at least three moves with codes 0–5.
The start rows are (−1, 1) and (0, −1), and no sequence of at most two row operations reaches
the identity rows; we check the at most 1 + 14 + 14² sequences by cases. The exponent-matrix
budget is the matrix part of T00156's tail bound (`TailBound.lean`, `expQ_move`,
`matrix_bound`); the definitions and proofs here are our own.
-/

namespace Floor

/-- A row: (x-sum, y-sum). -/
abbrev Row := ℤ × ℤ

/-- Two rows, one per relator. -/
abbrev Mat := Row × Row

/-- The exponent-sum homomorphism into `Multiplicative (ℤ × ℤ)`. -/
def ex : F2 →* Multiplicative Row :=
  FreeGroup.lift ![Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (0, 1)]

/-- The exponent sums of a word. -/
def e (w : F2) : Row := Multiplicative.toAdd (ex w)

@[simp] theorem e_mul (a b : F2) : e (a * b) = e a + e b := by simp [e]

@[simp] theorem e_inv (a : F2) : e a⁻¹ = -e a := by simp [e]

@[simp] theorem e_zpow (a : F2) (z : ℤ) : e (a ^ z) = z • e a := by simp [e]

@[simp] theorem e_gx : e gx = (1, 0) := by simp [e, ex, gx]

@[simp] theorem e_gy : e gy = (0, 1) := by simp [e, ex, gy]

theorem e_conj (g a : F2) : e (g * a * g⁻¹) = e a := by simp

theorem e_conj' (g a : F2) : e (g⁻¹ * a * g) = e a := by simp

/-- The rows of a pair. -/
def expQ (p : Pair) : Mat := (e p.1, e p.2)

/-- The row operation of a move; conjugations fix the rows. -/
def rowAct : Move → Mat → Mat
  | .c0, A => (-A.1, A.2)
  | .c1, A => (A.1, -A.2)
  | .c2, A => (A.1 + A.2, A.2)
  | .c3, A => (A.1 - A.2, A.2)
  | .c4, A => (A.1, A.2 + A.1)
  | .c5, A => (A.1, A.2 - A.1)
  | _, A => A

/-- Apply the row operations of a list of moves, first move first. -/
def rowList : List Move → Mat → Mat
  | [], A => A
  | m :: ms, A => rowList ms (rowAct m A)

theorem expQ_apply (m : Move) (p : Pair) : expQ (apply m p) = rowAct m (expQ p) := by
  cases m <;> simp only [expQ, apply, rowAct, e_mul, e_inv, sub_eq_add_neg] <;>
    rw [Prod.mk.injEq] <;> constructor <;> abel

theorem expQ_applyList (ms : List Move) (p : Pair) :
    expQ (applyList ms p) = rowList ms (expQ p) := by
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih => simp only [applyList_cons, ih, expQ_apply, rowList]

theorem rowAct_conj (m : Move) (hm : m.IsConj) (A : Mat) : rowAct m A = A := by
  cases m <;> simp only [Move.IsConj, Move.code] at hm <;> first | omega | rfl

/-- Conjugation moves can be dropped from a row computation. -/
theorem rowList_filter (ms : List Move) (A : Mat) :
    rowList ms A = rowList (ms.filter (fun m => !decide m.IsConj)) A := by
  induction ms generalizing A with
  | nil => rfl
  | cons m ms ih =>
    by_cases hm : m.IsConj
    · simp [rowList, hm, rowAct_conj m hm, ih]
    · simp [rowList, hm, ih]

/-- The identity rows. -/
def Mone : Mat := ((1, 0), (0, 1))

/-- The start rows of `S01 n`. -/
def A01 : Mat := ((-1, 1), (0, -1))

theorem expQ_standard : expQ standard = Mone := by simp [expQ, standard, Mone]

/-- **L6, start rows.** `expQ (S01 n) = ((−1, 1), (0, −1))` for every `n`. -/
theorem expQ_S01 (n : ℕ) : expQ (S01 n) = A01 := by
  simp only [expQ, S01, P, Q, e_mul, e_inv, e_zpow, e_gx, e_gy, A01]
  ext <;> simp
  ring

/-- **Two-move exclusion, by cases.** At most two row operations never take the start rows of
`S01 n` to the identity. -/
theorem no_short_rows : ∀ L : List Move, L.length ≤ 2 → rowList L A01 ≠ Mone
  | [], _ => by decide
  | [m], _ => by cases m <;> decide
  | [m1, m2], _ => by cases m1 <;> cases m2 <;> decide
  | _ :: _ :: _ :: _, h => by simp at h

/-- **L6.** Every route from `S01 n` to (x, y) has at least three moves with codes 0–5. -/
theorem three_nonconj (n : ℕ) (ms : List Move) (h : applyList ms (S01 n) = standard) :
    3 ≤ nonconjCount ms := by
  have hrow : rowList (ms.filter (fun m => !decide m.IsConj)) A01 = Mone := by
    rw [← rowList_filter, ← expQ_S01 n, ← expQ_applyList, h, expQ_standard]
  by_contra hlt
  exact no_short_rows _ (by unfold nonconjCount at hlt; omega) hrow

end Floor
