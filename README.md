# A linear lower bound for single-letter AC routes in the S01 family

A Lean 4 proof at the SAIR Proof Track pin (Lean `4.29.1`, Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`).

**Move unit.** Work with ordered pairs of words in the free group $F(x,y)$. One move is one of the fourteen ac-r2-v1 codes: invert either relator; right-multiply either relator by the other or its inverse; or conjugate either relator by one of $x,x^{-1},y,y^{-1}$. Free reduction costs no move. See the [official move specification](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/verifier/data/move_spec.json). This argument gives no lower bound growing with $n$ when conjugation by an arbitrary word costs one move.

**Theorem.** For every integer $n\geq4$, every finite route of these moves from the ordered relator pair
$$
R_n=\bigl(y^{-1}x^{-1}yx^{-1}yx,\;y^{-n}x^{-1}y^{n-1}x\bigr)
$$
to the exact ordered pair $(x,y)$ has length at least
$$
3+\left\lfloor\frac{n-1}{2}\right\rfloor.
$$
The presentation $\langle x,y\mid R_n\rangle$ and its relator pair are denoted `S01(n)` below.

**Proof outline.** A bounded-conjugator obstruction forces at least $\lfloor(n-1)/2\rfloor$ conjugation codes. Exponent sums force at least three inversion or multiplication codes. These disjoint classes of moves account for the stated sum. The argument is detailed below.

For $n=4,\ldots,11$, these are the eight supplied official puzzle presentations. S01 is our name for the family. `Floor/S01.lean` contains their official description strings verbatim and proves by `decide` that each parses to `some (S01 n)`. For other $n$, the result concerns the symbolic family only.

## Formal statements

The following declarations are in namespace `Floor`; `/` is natural-number division.

```lean
theorem s01_floor (n : ℕ) (hn : 4 ≤ n) (ms : List Move)
    (h : applyList ms (S01 n) = standard) : 3 + (n - 1) / 2 ≤ ms.length

theorem s01_floor_official (n : ℕ) (hn : 4 ≤ n) (ms : List Move)
    (h : toRel (applyList ms (S01 n)) = AC.standard 2) : 3 + (n - 1) / 2 ≤ ms.length

theorem route_reachable (n : ℕ) (ms : List Move) (h : applyList ms (S01 n) = standard) :
    AC.Reachable (toRel (S01 n)) (AC.standard 2)
```

`toRel` turns an ordered pair into the official `AC.Relators 2` tuple and sends `standard = (x,y)` to `AC.standard 2`. Accordingly, `s01_floor_official` changes the endpoint notation while still counting the same code list. `apply_sound` and `applyList_sound` give qualitative soundness in the official `AC.Reachable` relation. The implementations of codes 3 and 5 use three official steps; no minimal implementation length is asserted.

**Scope of the formalization.** The Lean development proves the lower bound, not its attainment, an exact shortest-route length, or existence of a route. Route existence for this family follows from earlier work, as explained under Related work; that result is not formalized here. The theorems do not prove or disprove AC or Stable AC. Their numerical conclusion is in ac-r2-v1 units, whereas one official `AC.Step` may conjugate by any word.

## Proof

1. **Bounded-conjugate subgroups** (`Bounded.lean`). For an ordered relator pair $R=(r_0,r_1)$, define
   $$
   H_R(k)=\langle u r_i u^{-1}: |u|\leq k,\ i=0,1\rangle\leq F(x,y),
   $$
   where $|u|$ is reduced word length and the brackets mean ordinary subgroup generation. This is `H R k` in Lean. Codes 0–5 preserve $H_R(k)$. For a conjugation code $m$, $H_{\operatorname{apply}(m,R)}(k)\subseteq H_R(k+1)$. Transporting membership backwards along a route to $(x,y)$ gives $x,y\in H_R(c)$, where $c$ is the number of conjugation codes (`route_mem`).

2. **Start bound** (`Action.lean`). Suppose $2k+2<n$. Put $c=n-k-1$, and let $A$ be the forward cycle on the integers $c,c+1,\ldots,n+k$, fixing all other integers. Let $T(h)=h+1$. Define a left action of the free group by $y\mapsto T$, $x\mapsto T A^{-1}$, with the rightmost permutation acting first. Every word of length at most $k$ sends 0 into $[-k,k]$. Both relators fix every integer in this latter interval. For $|u|\leq k$, apply the same estimate to $u^{-1}$: the relator fixes $u^{-1}\cdot0$, so $u r_i u^{-1}$ fixes 0. Hence all of $H_{R_n}(k)$ fixes 0, while $y\cdot0=1$. Thus $y\notin H_{R_n}(k)$ (`s01_start`). Taking $k=\lfloor(n-3)/2\rfloor$ forces at least $k+1=\lfloor(n-1)/2\rfloor$ conjugation codes.

3. **Three other codes** (`Matrix.lean`). The exponent-sum rows, in the order $x,y$, are $(-1,1)$ and $(0,-1)$. Codes 0–5 negate a row or add or subtract the other row. Conjugation leaves both rows unchanged. No sequence of at most two such row operations reaches the identity matrix; the finite check is proved by `decide`. Every route therefore has at least three non-conjugation codes (`three_nonconj`).

4. **Assembly** (`Floor.lean`). Every code belongs to exactly one of these two classes. Add their lower bounds (`length_eq_counts`, `s01_floor`).

## Files

| File | Content |
|---|---|
| `Floor/Moves.lean` | the 14 move codes on pairs of free-group words, `toRel` into `AC.Relators 2`, `apply_sound` |
| `Floor/Bounded.lean` | `H R k`, invariance under codes 0 to 5, radius cost at most one for codes 6 to 13, `route_mem`, `H standard 0 = ⊤` |
| `Floor/S01.lean` | `S01 n`, a parser for the official presentation text, kernel-checked equality with the official texts for n = 4..11 |
| `Floor/Matrix.lean` | exponent-sum rows, `three_nonconj` |
| `Floor/Action.lean` | the action on ℤ and `s01_start` |
| `Floor/Floor.lean` | `s01_floor`, `s01_floor_official`, `route_reachable` |

## Build

Start from the official `competition/tools/lean` folder, keep its `AC.lean` and `lean-toolchain` unchanged, add this `Floor/` folder beside `AC.lean`, and append this stanza to its `lakefile.toml` (the only change to an official file):

```toml
[[lean_lib]]
name = "Floor"
globs = ["Floor.+"]
```

Then build as in the official README, except that the whole Mathlib cache is fetched (`Floor` imports more of Mathlib than `AC` does) and the added library is built explicitly:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get
lake build
lake build Floor
```

`#print axioms` on `Floor.s01_floor`, `Floor.s01_floor_official` and `Floor.route_reachable` reports `propext`, `Classical.choice`, `Quot.sound` only. No `sorry`, `native_decide`, `implemented_by`, `axiom`, `unsafe` or `partial` appears in `Floor/`.

## Related work and attribution

Jonathan Patrick Gustafson (Team Bluepug), SAIR **ACC-P000016**, [repository at commit `2b153febfafe400f6d931c5e33686af0473154ff`](https://github.com/magicone2571/ac-tail-bound-lean-/tree/2b153febfafe400f6d931c5e33686af0473154ff), is the direct starting point: `Bluepug/TailBound.lean` adds an exponent-matrix budget to a radius-zero non-generation term. We replace that term by the bounded-conjugate subgroups $H_R(k)$. The name `expQ` follows that development. T00156 in our source comments denotes its team label. The code here is our own; no code from that contribution is copied or adapted.

The family belongs to the Miller–Schupp setting: Miller III–Schupp, *Some presentations of the trivial group*, Contemp. Math. 250 (1999), 113–115, [doi:10.1090/conm/250/03848](https://doi.org/10.1090/conm/250/03848). In the fixed free basis $a=y^{-1}x,\ t=y^{-1}$, our relators are AC-equivalent to
$$
\operatorname{MS}(n-1,w_*),\qquad w_*=t^{-1}ata^{-1},
$$
whose defining relations are $a^{-1}t^{n-1}a=t^n$ and $a=w_*$. The latter is equivalent to $t^{-1}at=a^2$. Shehper et al., [arXiv:2408.15332v2, Theorem 3](https://arxiv.org/abs/2408.15332v2), prove AC-triviality of this Miller–Schupp subfamily for every positive parameter. This identification supplies route existence for our family outside the Lean development; it does not preserve exact move counts.

Ajinkya Mulay's SAIR **ACC-P000013**, available through the [Proof Track](https://competition.sair.foundation/competitions/acc), studies the same Miller–Schupp subfamily and gives an exponent-matrix lower bound conditional on passage through a specified intermediate matrix. Our theorem concerns every route from the stated S01 pair; we make no claim to the first linear bound for this family.

Much larger lower bounds for other families are due to Bridson, [arXiv:1504.04187, Theorem A](https://arxiv.org/abs/1504.04187), in dihedral AC units with arbitrary conjugators, and Lishak, J. Topol. Anal. 9 (2017), 363–378, [doi:10.1142/S1793525317500182](https://doi.org/10.1142/S1793525317500182), using filling area and elementary Tietze transformations. Those results are not quantitative theorems about the S01 family.

Matrix descriptions of AC operations have classical precedents, including Myasnikov–Myasnikov–Shpilrain, *On the Andrews–Curtis equivalence*, Contemp. Math. 296 (2002), 183–198, [doi:10.1090/conm/296/05074](https://doi.org/10.1090/conm/296/05074). Single-letter counting conventions also appear in Miasnikov, IJAC 9 (1999), 671–686, [doi:10.1142/S0218196799000370](https://doi.org/10.1142/S0218196799000370), and Havas–Ramsay, IJAC 13 (2003), 61–68, [doi:10.1142/S0218196703001365](https://doi.org/10.1142/S0218196703001365). Their move and endpoint conventions need conversion before numerical comparison. Miasnikov–Myasnikov's [Theorem 1.1](https://arxiv.org/abs/math/0304305) concerns triviality by AC moves for total relator length at most twelve, not a growing bound here.

Bounded conjugator length is related to intrinsic filling diameter: see Riley, *Filling Functions*, [arXiv:math/0603059](https://arxiv.org/abs/math/0603059). Our use of this quantity is the explicit action proving $y\notin H_{R_n}(k)$ when $2k+2<n$, followed by the route-count argument.

Mathlib supplies `FreeGroup`, `FreeGroup.lift`, `FreeGroup.norm`, `Equiv.Perm`, `Subgroup.closure` and the tactics. SAIR supplies the unchanged `AC.lean`, the ac-r2-v1 move specification, and the eight official description strings copied into `S01.lean`.

Author: memcon.ai.
