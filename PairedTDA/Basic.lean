/-! Formal checks of selected parts of the paired persistent-homology permutation test.
    Core Lean 4 only (no Mathlib). -/

namespace PairedTDA

/-! ## 1. Label swaps -/

/-- A matched pair (tumour value, normal value) for one feature of one patient. -/
abbrev Pair := Int × Int

/-- Swap the tumour and normal labels of a pair when the flag is set. -/
def swapPair (s : Bool) (p : Pair) : Pair := if s then (p.2, p.1) else p

/-- Twice the pair midpoint (kept integral). -/
def mid2 (p : Pair) : Int := p.1 + p.2

/-- Swapping labels leaves the midpoint unchanged, so the feature ranking
    that uses midpoints is identical in every permutation. -/
theorem mid2_swap (s : Bool) (p : Pair) : mid2 (swapPair s p) = mid2 p := by
  cases s <;> simp [swapPair, mid2, Int.add_comm]

/-- The same holds for a whole feature (a list of patients' pairs) and any swap pattern. -/
theorem mid2_swap_list (ss : List Bool) (ps : List Pair) :
    (List.zipWith swapPair ss ps).map mid2 = (List.zipWith (fun _ p => p) ss ps).map mid2 := by
  induction ss generalizing ps with
  | nil => simp
  | cons s ss ih =>
    cases ps with
    | nil => simp
    | cons p ps => simp [List.zipWith, mid2_swap, ih]

/-- Swapping twice with the same flag restores the data. -/
theorem swap_swap (s : Bool) (p : Pair) : swapPair s (swapPair s p) = p := by
  cases s <;> simp [swapPair]

/-- Two swaps compose to the swap with the exclusive-or of the flags,
    so the set of swap patterns is a group acting on the data. -/
theorem swap_comp (s t : Bool) (p : Pair) : swapPair s (swapPair t p) = swapPair (xor s t) p := by
  cases s <;> cases t <;> simp [swapPair]

/-! ## 2. Sign invariance of the correlation distance -/

def dot : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

def neg (xs : List Int) : List Int := xs.map (fun x => -x)

theorem dot_neg_left (xs ys : List Int) : dot (neg xs) ys = - dot xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [neg, dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [neg, dot]
    | cons y ys =>
      have h := ih ys
      simp only [neg, List.map, dot] at h ⊢
      rw [h, Int.neg_mul, Int.neg_add]

theorem dot_neg_neg (xs ys : List Int) : dot (neg xs) (neg ys) = dot xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [neg, dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [neg, dot]
    | cons y ys =>
      have h := ih ys
      simp only [neg, List.map, dot] at h ⊢
      rw [h, Int.neg_mul_neg]

/-- Reversing the sign of one feature changes the covariance-type sum only by its sign,
    and leaves both sums of squares unchanged. Hence the squared correlation
    `(dot x y)^2 / (dot x x * dot y y)`, and so `d = sqrt (1 - r^2)`, does not change. -/
theorem sqcorr_sign_invariant (xs ys : List Int) :
    (dot (neg xs) ys) ^ 2 = (dot xs ys) ^ 2 ∧
    dot (neg xs) (neg xs) = dot xs xs ∧
    dot ys ys = dot ys ys := by
  refine ⟨?_, dot_neg_neg xs xs, rfl⟩
  have sq : ∀ z : Int, z ^ 2 = z * z := by
    intro z; rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  rw [dot_neg_left, sq, sq, Int.neg_mul_neg]

/-! ## 3. The plus-one permutation p-value -/

/-- Number of values in `l` that are at least `x` (including `x` itself when `x ∈ l`).
    For an observed value among the others, this is `1 + #{others >= x}`,
    the numerator of the plus-one p-value. -/
def pc (l : List Int) (x : Int) : Nat := (l.filter (fun y => decide (x ≤ y))).length

/-- Number of entries of `l` whose plus-one numerator is at most `k`. -/
def sel (l : List Int) (k : Nat) : Nat :=
  (l.filter (fun x => decide (pc l x ≤ k))).length

theorem exists_max : ∀ (l : List Int), l ≠ [] → ∃ a ∈ l, ∀ y ∈ l, y ≤ a
  | [], h => absurd rfl h
  | x :: t, _ => by
    by_cases ht : t = []
    · subst ht; exact ⟨x, by simp, by simp⟩
    · obtain ⟨a, ha, hmax⟩ := exists_max t ht
      by_cases hxa : x ≤ a
      · exact ⟨a, List.mem_cons_of_mem _ ha, by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hxa
          · exact hmax y hy⟩
      · exact ⟨x, by simp, by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact Int.le_refl _
          · have := hmax y hy; omega⟩

theorem pc_pos (l : List Int) (x : Int) (hx : x ∈ l) : 0 < pc l x := by
  unfold pc
  apply List.length_pos.mpr
  intro h
  have : x ∈ l.filter (fun y => decide (x ≤ y)) := List.mem_filter.mpr ⟨hx, by simp⟩
  rw [h] at this; simp at this

theorem pc_perm {l l' : List Int} (h : l.Perm l') (x : Int) : pc l x = pc l' x := by
  unfold pc
  exact (h.filter _).length_eq

theorem pc_cons_of_le (a : Int) (t : List Int) (x : Int) (hx : x ≤ a) :
    pc (a :: t) x = pc t x + 1 := by
  simp [pc, List.filter_cons, hx]

/-- **Counting lemma behind the plus-one p-value.** Among any `n` values, at most `k`
    have plus-one numerator `≤ k`. If the observed statistic and the permutation statistics
    are exchangeable, each of the `n` positions is equally likely to be the observed one,
    so `P(p ≤ k / n) ≤ k / n`: the plus-one p-value is valid (conservative if there are ties). -/
theorem sel_le : ∀ (n : Nat) (l : List Int), l.length = n → ∀ k : Nat, sel l k ≤ k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hn k
    by_cases hl : l = []
    · subst hl; simp [sel]
    · obtain ⟨a, ha, hmax⟩ := exists_max l hl
      obtain ⟨t, hperm⟩ : ∃ t, l.Perm (a :: t) := ⟨l.erase a, List.perm_cons_erase ha⟩
      have hlen : t.length < n := by
        have := hperm.length_eq
        simp at this; omega
      -- replace l by a :: t
      have hsel : sel l k = sel (a :: t) k := by
        unfold sel
        have e : ∀ x, pc l x = pc (a :: t) x := fun x => pc_perm hperm x
        have : l.filter (fun x => decide (pc l x ≤ k)) =
               l.filter (fun x => decide (pc (a :: t) x ≤ k)) := by
          apply List.filter_congr; intro x _; simp [e x]
        rw [this]
        exact ((hperm.filter _).length_eq)
      rw [hsel]
      have hmax' : ∀ y ∈ t, y ≤ a := fun y hy => hmax y (hperm.symm.subset (List.mem_cons_of_mem _ hy))
      cases k with
      | zero =>
        unfold sel
        have : (a :: t).filter (fun x => decide (pc (a :: t) x ≤ 0)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          have := pc_pos (a :: t) x hx
          simp; omega
        rw [this]; simp
      | succ k =>
        unfold sel
        rw [List.filter_cons]
        have hF : t.filter (fun x => decide (pc (a :: t) x ≤ k + 1)) =
                  t.filter (fun x => decide (pc t x ≤ k)) := by
          apply List.filter_congr; intro x hx
          rw [pc_cons_of_le a t x (hmax' x hx)]
          simp
        rw [hF]
        have hih := ih t.length hlen t rfl k
        unfold sel at hih
        split <;> simp <;> omega

end PairedTDA

