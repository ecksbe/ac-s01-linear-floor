import Floor.Bounded
import Floor.S01
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Tactic.FinCases

/-!
# Floor.Action — the start bound: `2k + 2 < n → y ∉ H (S01 n) k`

A permutation action of the free group on ℤ ("heights"):

* y acts as the shift `T : h ↦ h + 1`;
* `A = cyc c m` with `c = n - k - 1`, `m = 2k + 1` raises each height of the far band
  `c ≤ h < c + m = n + k` by one, sends `c + m` back to `c`, and fixes every other height;
* x acts as `T * A⁻¹`.

This is a left action (`ψ : F2 →* Perm ℤ`, `ψ (u * v) = ψ u * ψ v`), so no opposite group or
reversed evaluation is needed. Because `2k + 2 < n`, the heights `[-k, k + 1]` lie strictly
below `c`, so `A` fixes them pointwise. Then:

* `prefix_bound`: a word of letter length `≤ k` moves `0` to a height in `[-k, k]` (each letter
  moves heights below `c - 1` by exactly ±1);
* `P_fix`, `Q_fix`: `ψ P` and `ψ (Q n)` fix every height in `[-k, k]`
  (for `Q n` the far band carries `h + n - 1` to `h + n`);
* hence every generator `u r u⁻¹` of `H (S01 n) k` fixes `0` (`conj_fix`), while `ψ y` moves
  `0` to `1`.

Mathlib supplies `FreeGroup.lift` (the universal property) and `Equiv.Perm`.
-/

namespace Floor

/-! ### The two permutations -/

/-- Raise `c ≤ h < c + m` by one, send `c + m` to `c`, fix everything else. -/
def cyc (c : ℤ) (m : ℕ) : Equiv.Perm ℤ where
  toFun h := if c ≤ h ∧ h < c + m then h + 1 else if h = c + m then c else h
  invFun h := if c < h ∧ h ≤ c + m then h - 1 else if h = c then c + m else h
  left_inv h := by
    dsimp only
    split_ifs <;> omega
  right_inv h := by
    dsimp only
    split_ifs <;> omega

theorem cyc_of_lt {c : ℤ} {m : ℕ} {h : ℤ} (hh : h < c) : cyc c m h = h := by
  change (if c ≤ h ∧ h < c + m then h + 1 else if h = c + m then c else h) = h
  split_ifs <;> omega

theorem cyc_symm_of_lt {c : ℤ} {m : ℕ} {h : ℤ} (hh : h < c) : (cyc c m).symm h = h := by
  change (if c < h ∧ h ≤ c + m then h - 1 else if h = c then c + m else h) = h
  split_ifs <;> omega

theorem cyc_band {c : ℤ} {m : ℕ} {h : ℤ} (h1 : c ≤ h) (h2 : h < c + m) : cyc c m h = h + 1 := by
  change (if c ≤ h ∧ h < c + m then h + 1 else if h = c + m then c else h) = h + 1
  rw [if_pos ⟨h1, h2⟩]

/-- The shift `h ↦ h + 1`. -/
def T : Equiv.Perm ℤ := Equiv.addRight 1

@[simp] theorem T_apply (h : ℤ) : T h = h + 1 := rfl

@[simp] theorem T_inv_apply (h : ℤ) : T⁻¹ h = h - 1 := by
  rw [Equiv.Perm.inv_eq_iff_eq, T_apply]; ring

theorem T_zpow_apply (z : ℤ) : ∀ h : ℤ, (T ^ z) h = h + z := by
  induction z using Int.induction_on with
  | zero => intro h; simp
  | succ m ih =>
    intro h
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, T_apply]; ring
  | pred m ih =>
    intro h
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, T_inv_apply]; ring

/-- The image of x: first `A⁻¹`, then `T`. -/
def X (c : ℤ) (m : ℕ) : Equiv.Perm ℤ := T * (cyc c m)⁻¹

theorem X_apply (c : ℤ) (m : ℕ) (h : ℤ) : X c m h = (cyc c m).symm h + 1 := rfl

theorem X_inv_apply (c : ℤ) (m : ℕ) (h : ℤ) : (X c m)⁻¹ h = cyc c m (h - 1) := by
  rw [Equiv.Perm.inv_eq_iff_eq, X_apply, Equiv.symm_apply_apply]; ring

/-- The action: x ↦ `X c m`, y ↦ `T`. -/
def ψ (c : ℤ) (m : ℕ) : F2 →* Equiv.Perm ℤ := FreeGroup.lift ![X c m, T]

@[simp] theorem ψ_gx (c : ℤ) (m : ℕ) : ψ c m gx = X c m := by
  simp [ψ, gx, FreeGroup.lift_apply_of]

@[simp] theorem ψ_gy (c : ℤ) (m : ℕ) : ψ c m gy = T := by
  simp [ψ, gy, FreeGroup.lift_apply_of]

/-! ### Short words stay in the band `[-k, k]` -/

theorem ψ_letter (c : ℤ) (m : ℕ) (i : Fin 2) (b : Bool) :
    ψ c m (FreeGroup.mk [(i, b)]) = cond b (![X c m, T] i) (![X c m, T] i)⁻¹ := by
  simp [ψ, FreeGroup.lift_mk]

/-- One letter moves a height below `c - 1` by exactly ±1. -/
theorem letter_step (c : ℤ) (m : ℕ) (l : Letter) (h : ℤ) (hh : h + 1 < c) :
    ψ c m (FreeGroup.mk [l]) h = h + 1 ∨ ψ c m (FreeGroup.mk [l]) h = h - 1 := by
  obtain ⟨i, b⟩ := l
  rw [ψ_letter]
  fin_cases i <;> cases b
  · right
    simp (disch := omega) only [cond_false, Fin.zero_eta, Matrix.cons_val_zero, X_inv_apply,
      cyc_of_lt]
  · left
    simp (disch := omega) only [cond_true, Fin.zero_eta, Matrix.cons_val_zero, X_apply,
      cyc_symm_of_lt]
  · right
    simp [T_inv_apply]
  · left
    simp [T_apply]

/-- **Prefix lemma.** A letter list of length `≤ k` carries `0` into `[-length, length]`,
provided the band stays below `c - 1`. -/
theorem prefix_bound (c : ℤ) (m : ℕ) (k : ℕ) (hc : (k : ℤ) + 1 < c) :
    ∀ L : List Letter, L.length ≤ k →
      -(L.length : ℤ) ≤ ψ c m (FreeGroup.mk L) 0 ∧ ψ c m (FreeGroup.mk L) 0 ≤ L.length
  | [], _ => by rw [← FreeGroup.one_eq_mk]; simp
  | l :: L, hL => by
    have hL' : L.length ≤ k := by simp at hL; omega
    obtain ⟨ih1, ih2⟩ := prefix_bound c m k hc L hL'
    have e : FreeGroup.mk (l :: L) = FreeGroup.mk [l] * FreeGroup.mk L := by
      rw [FreeGroup.mul_mk]; rfl
    rw [e, map_mul, Equiv.Perm.mul_apply]
    have hlen : ((l :: L).length : ℤ) = L.length + 1 := by simp
    have hk : (L.length : ℤ) + 1 ≤ k := by simp at hL; omega
    rcases letter_step c m l (ψ c m (FreeGroup.mk L) 0) (by omega) with h | h <;>
      rw [h, hlen] <;> constructor <;> omega

theorem short_bound (c : ℤ) (m : ℕ) (k : ℕ) (hc : (k : ℤ) + 1 < c) {u : F2} (hu : u ∈ Short k) :
    -(k : ℤ) ≤ ψ c m u 0 ∧ ψ c m u 0 ≤ k := by
  obtain ⟨L, hL, rfl⟩ := hu
  obtain ⟨h1, h2⟩ := prefix_bound c m k hc L hL
  constructor <;> omega

/-! ### The relators fix the band -/

/-- `ψ P` fixes every height `h` with `h + 1 < c`, in particular the band `[-k, k]`. -/
theorem P_fix (c : ℤ) (m : ℕ) (h : ℤ) (hh : h + 1 < c) : ψ c m P h = h := by
  simp only [P, map_mul, map_inv, ψ_gx, ψ_gy, Equiv.Perm.mul_apply, T_apply, T_inv_apply,
    X_apply, X_inv_apply]
  simp (disch := omega) only [cyc_of_lt, cyc_symm_of_lt]
  ring

/-- `ψ (Q n)` fixes every height `h` with `h + 1 < c`, `c ≤ h + n - 1 < c + m`. -/
theorem Q_fix (n : ℕ) (c : ℤ) (m : ℕ) (h : ℤ) (hh : h + 1 < c) (h1 : c ≤ h + n - 1) (h2 : h + n - 1 < c + m) :
    ψ c m (Q n) h = h := by
  simp only [Q, map_mul, map_inv, map_zpow, ψ_gx, ψ_gy, Equiv.Perm.mul_apply, T_zpow_apply,
    X_apply, X_inv_apply]
  simp (disch := omega) only [cyc_band, cyc_symm_of_lt]
  ring

/-! ### The stabiliser of `0` -/

/-- The words whose image fixes `0`. -/
def stab0 (c : ℤ) (m : ℕ) : Subgroup F2 where
  carrier := {w | ψ c m w 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, Equiv.Perm.mul_apply] at *
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_inv] at *
    rw [Equiv.Perm.inv_eq_iff_eq, ha]

theorem conj_fix {c : ℤ} {m : ℕ} {u r : F2} (hr : ψ c m r (ψ c m u⁻¹ 0) = ψ c m u⁻¹ 0) :
    ψ c m (u * r * u⁻¹) 0 = 0 := by
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hr,
    ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

/-- **L7, the start bound.** If `2k + 2 < n`, then y is not in `H (S01 n) k`. -/
theorem s01_start (n k : ℕ) (hk : 2 * k + 2 < n) : gy ∉ H (S01 n) k := by
  set c : ℤ := (n : ℤ) - k - 1 with hc
  have hkc : (k : ℤ) + 1 < c := by omega
  have hle : H (S01 n) k ≤ stab0 c (2 * k + 1) := by
    rw [H, Subgroup.closure_le]
    rintro w ⟨u, hu, rfl | rfl⟩ <;>
      obtain ⟨b1, b2⟩ := short_bound c (2 * k + 1) k hkc (short_inv hu) <;>
      apply conj_fix
    · exact P_fix c _ _ (by omega)
    · exact Q_fix n c _ _ (by omega) (by omega) (by push_cast; omega)
  intro hy
  have h0 : ψ c (2 * k + 1) gy 0 = 0 := hle hy
  rw [ψ_gy, T_apply] at h0
  omega

end Floor
