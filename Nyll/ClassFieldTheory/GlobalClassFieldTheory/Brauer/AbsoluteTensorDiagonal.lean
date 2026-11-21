/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.RelativeRestrictionKernel
public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.AbsoluteTensorShapiro

/-! # Localization of actual diagonal classes for arbitrary finite extensions -/

@[expose] public section

open AlgebraicNumberTheory.Valuations CategoryTheory ContinuousCohomology
open Field.absoluteGaloisGroup IsDedekindDomain NumberField
open scoped NumberField TensorProduct

noncomputable section
namespace ClassFieldTheory.Brauer

section Diagonal

variable {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L/K)
local notation "Ω" => SeparableClosure F
attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower
attribute [local instance] scalarTensorUnitsAction

/-- The diagonal into the actual tensor units restricts the corresponding
global relative class along the canonical completed embedding. -/
theorem tensorH2ToCompletedBrauer_diagonal_of_embedding (v : AbsoluteValue K ℝ)
    (hv : v.IsNontrivial)
    (w : AbsoluteValueExtension v L) (e : v.Completion ≃ₐ[K] F)
    (i : L →ₐ[K] SeparableClosure K) (x : continuousCohomology 2 (galoisUnitsRep K L)) :
    tensorH2ToCompletedBrauer v hv w e
      (groupCohomology.map (MonoidHom.id G) (tensorDiagonalRepHom F) 2
        (discreteOriginalH2Equiv (galoisUnitsRep K L) x)) =
      restrict (algebraMap K F) (relativeInflationOfEmbedding i x) := by
  let f := algebraMap K F
  let u := separableClosureLift f
  let s := separableMap f
  let U : SeparableClosure K →ₐ[K] Ω :=
    { u with commutes' := separableClosureLift_algebraMap f }
  let j := U.comp i
  rw [tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map v hv w e j]
  let A := Rep.ofAlgebraAutOnUnits K L
  let B := Rep.ofMulDistribMulAction G (F ⊗[K] L)ˣ
  let r := ContinuousMonoidHom.id G
  let t := embeddedGaloisRestriction (B := F) j
  let p : Rep.res r.toMonoidHom A ⟶ B := tensorDiagonalRepHom (K := K) (L := L) F
  let α := discreteTopRepMap r p
  let β := absoluteTensorUnitsMap j
  let γ := galoisUnitsMap t j.toRingHom (embeddedGaloisRestriction_commutes j)
  let η : TopRep.res (r.comp t).toMonoidHom (galoisUnitsRep K L) ⟶ unitsRep F :=
    (TopRep.resFunctor t.toMonoidHom).map α ≫ β
  have hcoeff (a : galoisUnitsRep K L) : γ a = β (α a) := by
    let a₀ : Additive Lˣ := a
    let z : Additive (F ⊗[K] L)ˣ := p a
    let c (u : Additive Ωˣ) : Ω := (u.toMul : Ω)
    have hα : α a = z := rfl
    have hγ : c (γ a) = j (a₀.toMul : L) :=
      congrArg c (galoisUnitsMap_apply t j.toRingHom (embeddedGaloisRestriction_commutes j) a)
    have hβ : c (β z) = absoluteTensorEvaluation j (z.toMul : F ⊗[K] L) :=
      congrArg c (absoluteTensorUnitsMap_apply j z)
    have hz : (z.toMul : F ⊗[K] L) = (1 : F) ⊗ₜ[K] (a₀.toMul : L) := rfl
    have hEval : absoluteTensorEvaluation j (z.toMul : F ⊗[K] L) = j (a₀.toMul : L) := by
      rw [hz, absoluteTensorEvaluation_tmul, map_one, one_mul]
    apply Additive.toMul.injective
    apply Units.ext
    exact hγ.trans (((congrArg (fun y : Additive (F ⊗[K] L)ˣ => c (β y)) hα).trans
      (hβ.trans hEval)).symm)
  have hdiag : ContinuousCohomology.map t γ 2 = ContinuousCohomology.map (r.comp t) η 2 :=
    map_eq_of_values 2 γ η (fun _ => rfl) hcoeff
  have hmaps := ContinuousCohomology.map_comp r t α β 2
  have hp := (discreteTopRepH2Equiv_map r p x).trans
    (congrArg (groupCohomology.map r.toMonoidHom p 2)
      (galoisUnitsDiscreteH2_eq_original (K := K) (E := L) x))
  have hβ : (discreteTopRepH2Equiv B).symm
      (groupCohomology.map r.toMonoidHom p 2
        (discreteOriginalH2Equiv (galoisUnitsRep K L) x)) =
        ContinuousCohomology.map r α 2 x :=
    ((discreteTopRepH2Equiv B).symm_apply_eq).mpr hp.symm
  have hgroup (σ : Gal(Ω/F)) :
      embeddedGaloisRestriction i (s σ) = t σ := by
    apply AlgEquiv.ext
    intro a
    apply j.injective
    change u (i (embeddedGaloisRestriction i (s σ) a)) = j (t σ a)
    rw [embeddedGaloisRestriction_commutes, separableMap_commutes,
      embeddedGaloisRestriction_commutes]
    rfl
  have hcomp := galoisUnitsCohomologyMap_comp (embeddedGaloisRestriction i) s t
    i.toRingHom u j.toRingHom (embeddedGaloisRestriction_commutes i)
    (separableMap_commutes f) (embeddedGaloisRestriction_commutes j) hgroup (fun _ => rfl)
  change ContinuousCohomology.map t β 2
      ((discreteTopRepH2Equiv B).symm
        (groupCohomology.map r.toMonoidHom p 2
          (discreteOriginalH2Equiv (galoisUnitsRep K L) x))) = _
  rw [hβ]
  exact (ConcreteCategory.congr_hom (hdiag.trans hmaps) x).symm.trans
    (ConcreteCategory.congr_hom hcomp x)

end Diagonal

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] (i : L →ₐ[K] SeparableClosure K)

omit [NumberField L] in
/-- The generic finite tensor map localizes the actual relative diagonal. -/
theorem finiteTensorH2ToBrauerOfExtension_diagonal (v : HeightOneSpectrum (𝓞 K))
    (x : continuousCohomology 2 (galoisUnitsRep K L)) :
    finiteTensorH2ToBrauerOfExtension L v
      (groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom (v.adicCompletion K)) 2
        (discreteOriginalH2Equiv (galoisUnitsRep K L) x)) =
      finitePlaceRestriction K v (relativeInflationOfEmbedding i x) :=
  tensorH2ToCompletedBrauer_diagonal_of_embedding _ _ _ _ i x

omit [NumberField K] [NumberField L] in
/-- The generic infinite tensor map localizes the actual relative diagonal. -/
theorem infiniteTensorH2ToBrauerOfExtension_diagonal (v : InfinitePlace K)
    (x : continuousCohomology 2 (galoisUnitsRep K L)) :
    infiniteTensorH2ToBrauerOfExtension L v
      (groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom v.Completion) 2
        (discreteOriginalH2Equiv (galoisUnitsRep K L) x)) =
      infinitePlaceRestriction K v (relativeInflationOfEmbedding i x) :=
  tensorH2ToCompletedBrauer_diagonal_of_embedding _ _ _ _ i x

end ClassFieldTheory.Brauer
