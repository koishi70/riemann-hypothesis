module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

theorem FlagInjSumBound.finset_sum_bound (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S' hlt ih =>
    have hm : m ∉ S' := fun h => lt_irrefl m (hlt m h)
    rw [Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]
    obtain ⟨hs, _⟩ := ih
    refine ⟨?_, fun heq x hx => Finset.mem_range.2 ?_⟩
    · suffices S'.card ≤ m by omega
      simpa using Finset.card_le_card (show S' ⊆ Finset.range m from fun x hx => Finset.mem_range.2 (hlt x hx))
    · suffices x ≤ m by omega
      rcases Finset.mem_insert.1 hx with rfl | hx
      exacts [le_rfl, (hlt x hx).le]

theorem FlagInjSumBound.proof : FlagInjSumBound.Statement := by
  intro N g hg
  classical
  obtain ⟨hs, he⟩ := FlagInjSumBound.finset_sum_bound (Finset.univ.image g)
  rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin,
    Finset.sum_range_id, Finset.sum_image (fun i _ j _ h => hg h)] at hs he
  exact ⟨hs, fun h i => Finset.mem_range.1 (he h (Finset.mem_image_of_mem g (Finset.mem_univ i)))⟩

end GroundTheory.Heights₂.Heights.RestTerms
