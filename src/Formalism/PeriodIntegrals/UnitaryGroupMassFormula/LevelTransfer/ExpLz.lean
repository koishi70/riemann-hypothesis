module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.LzOutRight
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

open Matrix
noncomputable section

namespace PIQnLT

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem exp_Lz (hL : LevHom) (Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    NormedSpace.exp (Lz k i r' Y) = ιLev k i r' (NormedSpace.exp Y) := by
  letI : ∀ n : ℕ, NormedRing (Matrix (Fin n) (Fin n) ℂ) := fun _ => Matrix.linftyOpNormedRing
  letI : ∀ n : ℕ, NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := fun _ => Matrix.linftyOpNormedAlgebra
  rw [ιLev_eq, show ιLev k i r' 0 = 1 - Lz k i r' 1 by
    rw [← Lz_one (k := k) (i := i) (r' := r') hL]
    abel]
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (Lz k i r' Y)).unique
  rw [show (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (Lz k i r' Y) ^ n) =
      (fun n : ℕ => LzL k i r' ((n.factorial : ℂ)⁻¹ • Y ^ n) +
        (if n = 0 then 1 - Lz k i r' 1 else 0)) by
    funext n
    cases n with
    | zero => simp [LzL_apply]
    | succ m => rw [if_neg (Nat.succ_ne_zero m), add_zero, LinearMap.map_smul, LzL_apply, Lz_pow hL]]
  exact ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).map
    (LzL k i r') (LzL k i r').continuous_of_finiteDimensional).add (hasSum_ite_eq 0 _)

end PIQnLT
