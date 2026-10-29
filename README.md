# lean-paired-tda

Lean 4 proofs of four elementary properties of a paired permutation test on persistence diagrams. Core Lean only (no Mathlib). Lean 4.15.0.

Proved in `Method.lean`:

1. Swapping tumour and normal labels does not change the pair midpoint (`mid2_swap`, `mid2_swap_list`), so a feature ranking based on midpoints is identical in every permutation.
2. Label swaps form a group: `swap_swap` and `swap_comp`.
3. Reversing the sign of a feature leaves the squared correlation, and so the distance sqrt(1 - r^2), unchanged (`dot_neg_left`, `dot_neg_neg`, `sqcorr_sign_invariant`).
4. Counting lemma for the plus-one p-value (`sel_le`): among n values, at most k have plus-one numerator at most k. Under exchangeability this gives P(p <= k/n) <= k/n.

Not covered: exchangeability of the data after alignment (an assumption), the persistence computation, the W2 distance, and calibration by simulation.

Check: `lean Method.lean` (no errors, no `sorry`).
