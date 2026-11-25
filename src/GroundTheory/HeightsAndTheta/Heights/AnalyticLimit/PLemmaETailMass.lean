module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncTail
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh)

theorem LemmaETailMass.proof (hT : LemmaETrunc.Statement) (hC : LemmaETruncMass.Statement)
    (hB : LemmaETruncTail.Statement) : LemmaETailMass.Statement := by
  intro X _ _ _ D A Om L s hL hs hd hle C₁ hC₁
  obtain ⟨K, hK0, hK⟩ := hB D A Om L s hL hs hd hle
  refine ⟨(C₁ + 2) ^ D * K, fun u hu R₀ hR₀ => ?_⟩
  let tr := fun (R : ℝ) (i : Fin D) =>
    hT A Om (secOpen s) (rSec L s) C₁ (u i) (isOpen_secOpen hL hs) hd
      (fun x _ => exp_one_le_rSec hle x) hC₁ (hu i).smooth (hu i).nonneg (hu i).nonpos
      (hu i).le_u (hu i).smooth_or_pole (max (Real.exp 1) R) (le_max_left _ _)
  let v := fun (R : ℝ) (i : Fin D) => (tr R i).choose
  obtain ⟨hint, hb⟩ := hC D A Om (secOpen s) (rSec L s) u v (isOpen_secOpen hL hs)
    (continuousOn_rSec hL hs) (fun i => (hu i).smooth) (fun i => (hu i).nonneg)
    (fun R hR i => ⟨(tr R i).choose_spec.1, (tr R i).choose_spec.2.1, by
      simpa only [max_eq_right hR] using (tr R i).choose_spec.2.2.2⟩) R₀ hR₀
  have hlog : 1 ≤ Real.log R₀ := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hR₀
  have hM : 1 ≤ C₁ * Real.log R₀ + 2 := by nlinarith
  refine ⟨hint, hb.trans <| (hK _ hM (v R₀) (fun i => (tr R₀ i).choose_spec.1)
    (fun i => (tr R₀ i).choose_spec.2.1) (fun i x => by
      simpa only [max_eq_right hR₀] using (tr R₀ i).choose_spec.2.2.1 x) R₀ hR₀).trans ?_⟩
  apply div_le_div_of_nonneg_right _ ((Real.exp_pos 1).le.trans hR₀)
  rw [mul_right_comm ((C₁ + 2) ^ D) K, ← mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by linarith only [hM]) (by nlinarith only [hlog]) D) hK0

end GroundTheory.Heights₂.Heights.AnalyticLimit
