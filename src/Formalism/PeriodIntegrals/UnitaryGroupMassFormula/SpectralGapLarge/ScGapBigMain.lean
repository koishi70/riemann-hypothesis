module

public import Formalism.PeriodIntegrals.ScGapBig
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.Height.NumberField

@[expose] public section
namespace PI.UnitaryGroupMassFormula.ScGapBig
open PI.ScGapBig

theorem nat_bound (n m t : ℕ) (hn : 1801 ≤ n) (hm : m ≤ n + 1) (ht : t ≤ n + 6) :
    2 * (n + m * t) ^ 3 + t + 3 < 16 * n ^ 19 := by
  nlinarith [Nat.pow_le_pow_left (show n + m * t ≤ 2 * n ^ 2 by
      nlinarith [Nat.mul_le_mul hm ht, Nat.mul_le_mul_right n hn]) 3,
    Nat.mul_le_mul_left (n ^ 6) (show 2 ≤ n ^ 13 from
      (show 2 ≤ n by omega).trans (Nat.le_self_pow (by decide) n)),
    (show n ≤ n ^ 6 from Nat.le_self_pow (by decide) n)]

theorem scGapBig_main : ScGapBig := by
  intro k r b hn hgap
  have hrk : rk48 k r = 2 * r + k + 1 := rfl
  obtain ⟨t, hodd, hlo, hhi⟩ : ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ t ≤ rk48 k r + 6 :=
    ⟨2 * ((rk48 k r + 5) / 2) + 1, ⟨_, rfl⟩, by omega, by omega⟩
  refine ⟨t, hodd, hlo, by omega, fun j hj ↦ ?_⟩
  linarith [hgap j hj, show 2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 <
      16 * (rk48 k r : ℝ) ^ 19 by
        exact_mod_cast nat_bound (rk48 k r) (2 * r + 2) t hn (by omega) hhi]

end PI.UnitaryGroupMassFormula.ScGapBig
