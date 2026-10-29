# lean-paired-tda

Lean 4 proofs of properties of a paired permutation test on persistence diagrams. Lean 4.15.0, Mathlib v4.15.0.

## `PairedTDA/Basic.lean` (core Lean)

1. Swapping tumour and normal labels does not change the pair midpoint (`mid2_swap`, `mid2_swap_list`), so a feature ranking based on midpoints is identical in every permutation.
2. Label swaps form a group: `swap_swap`, `swap_comp`.
3. Reversing the sign of a feature leaves the squared correlation, and so the distance sqrt(1 - r^2), unchanged (`dot_neg_left`, `dot_neg_neg`, `sqcorr_sign_invariant`).
4. Counting lemma for the plus-one p-value on integer lists (`sel_le`).

## `PairedTDA/PlusOne.lean` (Mathlib, measure theory)

Let `x : Fin (m+1) -> R` hold the observed statistic (coordinate 0) and `m` permutation statistics, and let its law `mu` be a probability measure invariant under coordinate permutations (exchangeability). With `p = cnt x 0 / (m+1)`, where `cnt x 0 = 1 + #{j != 0 : x j >= x 0}`:

* `card_le`: for every real vector, at most `k` coordinates have `cnt <= k`.
* `prob_good_le`: `mu {cnt x 0 <= k} * (m+1) <= k`.
* `pvalue_valid`: `mu {p <= alpha} <= alpha` for every `alpha >= 0`. Ties are handled conservatively.

Exchangeability is a hypothesis of the theorem. Not covered: whether the data are exchangeable after alignment, the persistence computation, the W2 distance, and calibration by simulation.

## Build

Needs Lean 4.15.0 (see `lean-toolchain`). `lake update` then `lake build`. Building Mathlib from source takes a while unless the Mathlib cache is available (`lake exe cache get`).
