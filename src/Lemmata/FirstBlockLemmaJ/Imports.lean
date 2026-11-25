module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
@[expose] public section
universe u_1
namespace Bl.FirstBlockLemmaJ
theorem goal1 :
  ∀ {V : Type u_1} [inst : NormedAddCommGroup.{u_1} V] [inst_1 : NormedSpace.{0, u_1} Complex V] {g : V → Complex} {x : V}
  {ε : Real},
  DifferentiableOn.{0, u_1, 0} Complex g (Metric.ball.{u_1} x ε) →
    ∀ {z : V},
      Membership.mem.{u_1, u_1} (Metric.ball.{u_1} x ε) z →
        Filter.EventuallyEq.{u_1, 0} (nhds.{u_1} z) g 0 →
          ∀ (y : V), Membership.mem.{u_1, u_1} (Metric.ball.{u_1} x ε) y → Eq.{1} (g y) 0 := fun {V} _ _ {g x ε} hg {z} hz hz0 y hy => by
  let φ := AffineMap.const ℝ ℂ z + ((LinearMap.toSpanSingleton ℂ V (y - z)).restrictScalars ℝ).toAffineMap
  have hd : Differentiable ℂ φ := (differentiable_const z).add (differentiable_id.smul_const (y - z))
  simpa [φ, Function.comp_apply] using ((hg.comp hd.differentiableOn (Set.mapsTo_preimage _ _)).analyticOnNhd
    (Metric.isOpen_ball.preimage hd.continuous)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    ((convex_ball x ε).affine_preimage φ).isPreconnected (z₀ := 0) (by simpa [φ] using hz)
    (hz0.comp_tendsto (by simpa [φ] using hd.continuous.tendsto (0 : ℂ))) (x := 1) (by simpa [φ] using hy)
end Bl.FirstBlockLemmaJ
