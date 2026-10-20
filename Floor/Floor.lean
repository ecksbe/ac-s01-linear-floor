import Floor.Moves
import Floor.Bounded
import Floor.Matrix
import Floor.S01
import Floor.Action

/-!
# Floor.Floor — the whole-route floor on `S01 n`, in move-code units

For every `n ≥ 4`, every list of ac-r2-v1 move codes taking `S01 n` to (x, y) has length at
least `3 + ⌊(n-1)/2⌋`. The two budgets add because they count disjoint moves:

* conjugation moves (codes 6–13): by (★) `route_mem`, y ∈ `H (S01 n) (conjCount ms)`, and by
  `s01_start` with `k = ⌊(n-3)/2⌋`, y ∉ `H (S01 n) k`; so `conjCount ms ≥ k + 1 = ⌊(n-1)/2⌋`;
* non-conjugation moves (codes 0–5): `three_nonconj` gives at least three.

The unit is one move code, not one official `AC.Step` (one `AC.Step` may conjugate by any word).
`applyList_sound` shows that each such list is an official `AC.Reachable` path.
-/

namespace Floor

/-- Conjugation count: a route from `S01 n` needs more than `k` conjugations if `2k + 2 < n`. -/
theorem conj_lower (n k : ℕ) (hk : 2 * k + 2 < n) (ms : List Move)
    (h : applyList ms (S01 n) = standard) : k + 1 ≤ conjCount ms := by
  by_contra hlt
  have hy := (route_mem ms (S01 n) h).2
  exact s01_start n k hk (H_mono (S01 n) (by omega) hy)

/-- **The floor.** Every move-code route from `S01 n` to (x, y), `n ≥ 4`, has at least
`3 + (n - 1) / 2` moves. -/
theorem s01_floor (n : ℕ) (hn : 4 ≤ n) (ms : List Move)
    (h : applyList ms (S01 n) = standard) : 3 + (n - 1) / 2 ≤ ms.length := by
  have hc := conj_lower n ((n - 3) / 2) (by omega) ms h
  have hd := three_nonconj n ms h
  rw [length_eq_counts ms]
  omega

theorem toRel_injective : Function.Injective toRel :=
  fun _ _ h => Prod.ext (congrFun h 0) (congrFun h 1)

/-- The floor with the endpoint stated through the official relator type. -/
theorem s01_floor_official (n : ℕ) (hn : 4 ≤ n) (ms : List Move)
    (h : toRel (applyList ms (S01 n)) = AC.standard 2) : 3 + (n - 1) / 2 ≤ ms.length :=
  s01_floor n hn ms (toRel_injective (h.trans toRel_standard.symm))

/-- Such a move list is an official AC path from `toRel (S01 n)` to the standard tuple. -/
theorem route_reachable (n : ℕ) (ms : List Move) (h : applyList ms (S01 n) = standard) :
    AC.Reachable (toRel (S01 n)) (AC.standard 2) := by
  have := applyList_sound ms (S01 n)
  rwa [h, toRel_standard] at this

end Floor
