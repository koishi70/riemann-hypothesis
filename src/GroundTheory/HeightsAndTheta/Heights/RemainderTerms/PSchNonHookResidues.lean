module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur

@[expose] public section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open Finset

theorem sum_fin_staircase (k : ℕ) : ∑ i : Fin k, (k - 1 - (i : ℕ)) = k * (k - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k,
    Finset.sum_range_reflect (fun i : ℕ => i) k, Finset.sum_range_id]

theorem SchNonHookResidues.proof (h1 : SchResidueCount.Statement) :
    SchNonHookResidues.Statement := by
  intro k nu hk hanti hsum hnot
  push Not at hnot
  obtain ⟨j, hj0, hj2⟩ := hnot
  have hk2 : 1 < k := lt_of_le_of_lt (by omega : 1 ≤ (j : ℕ)) j.isLt
  by_contra hcon
  push Not at hcon
  let l (i : Fin k) := nu i + (k - 1 - (i : ℕ))
  have hcount := h1 k l (fun i => by
    rw [two_mul]
    exact add_lt_add_of_le_of_lt
      (hsum ▸ single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)) (by omega))
    (fun a b hab => Classical.byContradiction fun hne => hcon a b hne hab)
  rw [show ∑ i, l i = k + k * (k - 1) / 2 by
    simp only [l, sum_add_distrib, hsum, sum_fin_staircase]] at hcount
  have hmem (i : Fin k) (hi : (i : ℕ) ≤ 1) : i ∈ univ.filter (fun t => k ≤ l t) := by
    simp only [mem_filter, mem_univ, true_and, l]
    suffices nu j ≤ nu i by omega
    apply hanti
    change (i : ℕ) ≤ (j : ℕ)
    omega
  suffices k * 2 ≤ k * (univ.filter fun i => k ≤ l i).card by omega
  exact Nat.mul_le_mul_left k (one_lt_card.mpr
    ⟨_, hmem ⟨0, by omega⟩ (Nat.zero_le 1), _, hmem ⟨1, hk2⟩ le_rfl,
      fun e => Nat.zero_ne_one (congrArg Fin.val e)⟩)
end GroundTheory.Heights₂.Heights.RestTerms
