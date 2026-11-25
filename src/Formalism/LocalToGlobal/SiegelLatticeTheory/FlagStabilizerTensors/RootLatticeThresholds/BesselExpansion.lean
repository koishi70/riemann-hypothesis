module

public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

variable {D : D7}

private theorem one_le_of_le_and_inv_le {a x : ℝ} (ha : 0 < a) (h : a ≤ x) (hi : a⁻¹ ≤ x) :
    1 ≤ x :=
  (le_total 1 a).elim (fun h₁ => h₁.trans h) (fun h₁ => ((one_le_inv₀ ha).2 h₁).trans hi)

theorem frame_bounds {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) :
    2 ≤ b ∧ 1 ≤ b ^ (3 + Ch) ∧ D.host.rdE ≤ b ^ (3 + Ch) := by
  obtain ⟨⟨hk, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hb : 2 ≤ b := by
    nlinarith [b_ge_of_StdHyp0 hk hStd.to0,
      (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1)) :
        (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7)]
  obtain ⟨ha, h₁, h₂, -⟩ := hStd.2.2.2
  refine ⟨hb, ?_, Formalism.MainNotions.TheoremBConstants.rdE_le D b Ch hb ha h₂⟩
  rw [Real.rpow_add (by linarith : 0 < b)]
  nlinarith [one_le_of_le_and_inv_le ha h₁ h₂,
    Real.one_le_rpow (by linarith : 1 ≤ b) (by norm_num : (0 : ℝ) ≤ 3)]

theorem ch_nonneg {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) : 0 ≤ Ch := by
  by_contra! hc
  apply (Real.rpow_lt_one_of_one_lt_of_neg (by linarith [(frame_bounds hCg hok).1] : 1 < b) hc).not_ge
  obtain ⟨⟨-, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  exact one_le_of_le_and_inv_le hStd.2.2.2.1 hStd.2.2.2.2.1 hStd.2.2.2.2.2.1

end Formalism.L2.SG.Pf.BesselExpansion
