module
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
@[expose] public section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem fFun_mul_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k),
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν Ψ g h
  let f : Matrix (Fin a) (Fin a) k →* Matrix C C k :=
    { toFun := fun M => (Matrix.fromBlocks M 0 0 1).submatrix σ.symm σ.symm
      map_one' := by rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
      map_mul' := fun M N => by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp }
  let E : GL C k := Units.map f g
  rw [← Matrix.mul_assoc, show g.val * X0 k σ = X0 k σ * E.val by
        ext i j; rw [frameMatrixFirstColumnBlock_mul_apply]
        obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [X0, E, f, Matrix.mul_apply],
      Matrix.mul_assoc, show E.val * (invT h).val = (invT (invT E * h)).val by rw [map_mul, invT_invT, Units.val_mul]]
  rw [splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ,
      Units.val_mul, ← Matrix.mul_assoc, show Y0 k σ * (invT E).val = Y0 k σ by
        ext i j; rw [frameMatrixSecondColumnBlock_mul_apply, invT_val]
        obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [Y0, E, f, ← map_inv, Matrix.one_apply, eq_comm]]
  rw [gdet_mul, gdet_invT, show gdet E = gdet g by ext; simp [E, f, Matrix.det_submatrix_equiv_self],
      map_mul, map_inv, apow_mul, apow_inv, apow_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero (ν (gdet g)), apow_ne_zero (gdet g) ((Fintype.card C : ℂ) / 2)]
end GlobalTheory
