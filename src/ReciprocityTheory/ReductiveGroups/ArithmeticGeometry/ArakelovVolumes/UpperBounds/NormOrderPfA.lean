module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.LocalRing.LocalSubring

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd

theorem exists_val_of_prime {Kf : Type*} [Field Kf] (A : Subring Kf) (P : Ideal A) [P.IsPrime] :
    ∃ V : ValuationSubring Kf, (∀ a : A, (a : Kf) ∈ V) ∧ (∀ a : A, a ∉ P → (a : Kf)⁻¹ ∈ V) ∧
      ∀ a : A, a ∈ P → V.valuation (a : Kf) < 1 := by
  obtain ⟨V, hV⟩ := (LocalSubring.ofPrime A P).exists_le_valuationSubring
  obtain ⟨i, hi⟩ := LocalSubring.le_def.1 hV
  let R := (LocalSubring.ofPrime A P).toSubring
  have hmem (a : A) : (a : Kf) ∈ V := i (LocalSubring.le_ofPrime A P a.property)
  have hval (a : A) : V.valuation (a : Kf) = 1 ↔ a ∉ P :=
    (V.valuation_eq_one_iff (Subring.inclusion i (algebraMap A R a))).symm.trans
      ((isUnit_map_iff (Subring.inclusion i) _).trans
        (IsLocalization.AtPrime.isUnit_to_map_iff R P a))
  refine ⟨V, hmem, fun a ha => ?_, fun a ha => ?_⟩
  · rw [← V.valuation_le_one_iff, map_inv₀, (hval a).2 ha, inv_one]
  · exact ((V.valuation_le_one_iff _).2 (hmem a)).lt_of_ne fun h => (hval a).1 h ha

end ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd
