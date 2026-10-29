import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# Validity of the plus-one permutation p-value

`x : Fin (m+1) → ℝ` holds the observed statistic (coordinate `0`) and `m` permutation statistics.
If the law of `x` is invariant under permutations of the coordinates (exchangeability),
then `P(p ≤ α) ≤ α` for the plus-one p-value `p = cnt x 0 / (m+1)`, with ties handled
conservatively. Exchangeability is an assumption of the theorem, not a conclusion.
-/

open MeasureTheory Finset

namespace PlusOne

variable {n : ℕ}

/-- Number of coordinates at least as large as coordinate `i` (including `i` itself):
`1 + #{j ≠ i : x j ≥ x i}`, the numerator of the plus-one p-value. -/
noncomputable def cnt (x : Fin n → ℝ) (i : Fin n) : ℕ := (univ.filter (fun j => x i ≤ x j)).card

/-- Pointwise counting lemma: at most `k` coordinates have `cnt ≤ k`. -/
theorem card_le (k : ℕ) (x : Fin n → ℝ) :
    (univ.filter (fun i => cnt x i ≤ k)).card ≤ k := by
  by_contra h
  push_neg at h
  have hne : (univ.filter (fun i => cnt x i ≤ k)).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨i0, hi0, hmin⟩ := (univ.filter (fun i => cnt x i ≤ k)).exists_min_image x hne
  have hsub : (univ.filter (fun i => cnt x i ≤ k)) ⊆ univ.filter (fun j => x i0 ≤ x j) := by
    intro j hj
    simpa using hmin j hj
  have h1 := Finset.card_le_card hsub
  have h2 : cnt x i0 ≤ k := (Finset.mem_filter.mp hi0).2
  unfold cnt at h2
  omega

theorem cnt_comp (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    cnt (x ∘ σ) i = cnt x (σ i) := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp σ (fun l => if x (σ i) ≤ x l then 1 else 0)

theorem measurable_cnt (i : Fin n) : Measurable (fun x : Fin n → ℝ => cnt x i) := by
  have : (fun x : Fin n → ℝ => cnt x i) = fun x => ∑ j, if x i ≤ x j then 1 else 0 := by
    funext x; unfold cnt; rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))
    measurable_const measurable_const

theorem measurableSet_good (i : Fin n) (k : ℕ) : MeasurableSet {x : Fin n → ℝ | cnt x i ≤ k} :=
  (measurable_cnt i) (measurableSet_Iic (a := k))

variable {m : ℕ}

/-- Under exchangeability every coordinate is equally likely to have `cnt ≤ k`. -/
theorem measure_good_eq (μ : Measure (Fin (m+1) → ℝ))
    (hexch : ∀ σ : Equiv.Perm (Fin (m+1)), μ.map (fun x => x ∘ σ) = μ)
    (i : Fin (m+1)) (k : ℕ) :
    μ {x | cnt x i ≤ k} = μ {x | cnt x 0 ≤ k} := by
  set σ : Equiv.Perm (Fin (m+1)) := Equiv.swap 0 i
  have hmeas : Measurable (fun x : Fin (m+1) → ℝ => x ∘ σ) :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
  have h := hexch σ
  have hσ0 : σ 0 = i := Equiv.swap_apply_left 0 i
  calc μ {x | cnt x i ≤ k}
      = (μ.map (fun x => x ∘ σ)) {x | cnt x 0 ≤ k} := by
        rw [Measure.map_apply hmeas (measurableSet_good 0 k)]
        congr 1
        ext x
        simp [cnt_comp, hσ0]
    _ = μ {x | cnt x 0 ≤ k} := by rw [h]

/-- **Plus-one p-value is valid under exchangeability.** -/
theorem prob_good_le (μ : Measure (Fin (m+1) → ℝ)) [IsProbabilityMeasure μ]
    (hexch : ∀ σ : Equiv.Perm (Fin (m+1)), μ.map (fun x => x ∘ σ) = μ) (k : ℕ) :
    μ {x | cnt x 0 ≤ k} * (m + 1) ≤ k := by
  have hsum : ∑ i : Fin (m+1), μ {x | cnt x i ≤ k} = μ {x | cnt x 0 ≤ k} * (m + 1) := by
    simp [measure_good_eq μ hexch, mul_comm]
  rw [← hsum]
  have hint : ∑ i : Fin (m+1), μ {x | cnt x i ≤ k}
      = ∫⁻ x, ∑ i : Fin (m+1), ({x | cnt x i ≤ k}.indicator (fun _ => (1 : ENNReal)) x) ∂μ := by
    rw [lintegral_finset_sum _ (fun i _ => (measurable_const.indicator (measurableSet_good i k)))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := lintegral_indicator_one (μ := μ) (measurableSet_good i k)
    exact this.symm
  rw [hint]
  calc ∫⁻ x, ∑ i : Fin (m+1), ({x | cnt x i ≤ k}.indicator (fun _ => (1 : ENNReal)) x) ∂μ
      ≤ ∫⁻ _x, (k : ENNReal) ∂μ := by
        refine lintegral_mono (fun x => ?_)
        have : ∑ i : Fin (m+1), ({x | cnt x i ≤ k}.indicator (fun _ => (1 : ENNReal)) x)
            = ((univ.filter (fun i => cnt x i ≤ k)).card : ENNReal) := by
          simp [Set.indicator, Finset.sum_boole]
        rw [this]
        exact_mod_cast card_le k x
    _ = k := by simp

/-- **Level-`α` statement.** With `p = cnt x 0 / (m+1)`, `P(p ≤ α) ≤ α` for every `α ≥ 0`. -/
theorem pvalue_valid (μ : Measure (Fin (m+1) → ℝ)) [IsProbabilityMeasure μ]
    (hexch : ∀ σ : Equiv.Perm (Fin (m+1)), μ.map (fun x => x ∘ σ) = μ) (α : ℝ) (hα : 0 ≤ α) :
    μ {x | (cnt x 0 : ℝ) / (m + 1) ≤ α} ≤ ENNReal.ofReal α := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hset : {x : Fin (m+1) → ℝ | (cnt x 0 : ℝ) / (m + 1) ≤ α}
      = {x | cnt x 0 ≤ ⌊α * (m + 1)⌋₊} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [div_le_iff₀ hpos, Nat.le_floor_iff (by positivity)]
  rw [hset]
  have h1 := prob_good_le μ hexch ⌊α * (m + 1)⌋₊
  have h2 : ((⌊α * (m + 1)⌋₊ : ℕ) : ENNReal) ≤ ENNReal.ofReal α * ((m : ENNReal) + 1) := by
    have hfl : ((⌊α * (m + 1)⌋₊ : ℕ) : ℝ) ≤ α * (m + 1) := Nat.floor_le (by positivity)
    have : ENNReal.ofReal ((⌊α * (m + 1)⌋₊ : ℕ) : ℝ) ≤ ENNReal.ofReal (α * (m + 1)) :=
      ENNReal.ofReal_le_ofReal hfl
    rw [ENNReal.ofReal_natCast] at this
    rw [ENNReal.ofReal_mul hα] at this
    have e : ENNReal.ofReal ((m : ℝ) + 1) = (m : ENNReal) + 1 := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp
    rwa [e] at this
  have h3 := h1.trans h2
  have hne : ((m : ENNReal) + 1) ≠ 0 := by simp
  have hnt : ((m : ENNReal) + 1) ≠ ⊤ := by simp
  exact (ENNReal.mul_le_mul_right hne hnt).mp h3

end PlusOne
