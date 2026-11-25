module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Interface
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot

@[expose] public section
noncomputable section
open Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem norm_le_one_of_root {l : ℕ} [Fact l.Prime] {x : ℂ_[l]} (P : Polynomial ℤ) (hm : P.Monic)
    (h : P.eval₂ (Int.castRingHom ℂ_[l]) x = 0) : ‖x‖ ≤ 1 := by
  by_contra! hlt
  rw [hm.as_sum] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  cases hn : P.natDegree with
  | zero => simp [hn] at h
  | succ n =>
    rw [hn] at h
    refine (not_le_of_gt (pow_lt_pow_right₀ hlt (Nat.lt_succ_self n))) ?_
    rw [← norm_pow, eq_neg_of_add_eq_zero_left h, norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow, eq_intCast (Int.castRingHom ℂ_[l])]
    refine le_trans ?_ (pow_le_pow_right₀ hlt.le (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    exact mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_intCast_le_one _ _)

theorem jInt : JInt := by
  intro d L hsf hd hL l _ ι
  obtain ⟨P, hm, hP⟩ := cm1 d L hsf hd hL
  apply_fun (ι : ℂ →+* ℂ_[l]) at hP
  rw [Polynomial.hom_eval₂, map_zero] at hP
  refine norm_le_one_of_root P hm ?_
  exact (congrArg (fun f => P.eval₂ f _) (Subsingleton.elim _ _)).trans hP

end ReciprocityTheory.ChartRestriction.L1
