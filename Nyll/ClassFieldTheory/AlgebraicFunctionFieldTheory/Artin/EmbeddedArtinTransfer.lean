/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.PresentedRayArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteGaloisPresentation

/-!
# Original native Artin transfer for an explicitly embedded finite extension

The original embedding supplies its actual finite fixing subgroup and
fixed-field presentation. All degree-one comparison data are constructed
from that presentation. Thus original native reciprocity commutes with
original transfer for the actual upper field, with no fixed-field
presentation or reciprocity square supplied as a hypothesis.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FunctionField

open AlgebraicCurve ClassFormation LocalClassFieldTheory ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

section EmbeddedGroups

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] SeparableClosure K)

/-- The original finite absolute fixing subgroup determined by the actual embedding. -/
def embeddedTransferAbstractField : FiniteAbstractField Gal(SeparableClosure K/K) :=
  (FiniteGaloisSubextension.toFiniteAbstractFieldExtension
    (K := intrinsicFiniteAbstractBase K)
    (finiteGaloisAbstractExtensionOfEmbedding K L i)).field

local notation "H" => embeddedTransferAbstractField K L i
local notation "F" => abstractFixedField K (SeparableClosure K) (FiniteAbstractField.field H)
local notation "η" => finiteGaloisEmbeddedFixedFieldEquiv K L i

attribute [local instance]
  presentedFixedFieldSeparableClosureAlgebra presentedFixedFieldSeparableClosureSMul

/-- The embedded Galois field has a normal absolute fixing subgroup. -/
local instance embeddedTransferNormal : (H).field.toSubgroup.Normal := by
  change (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup.Normal
  infer_instance

/-- The fixed-field presentation uses the given field equivalence. -/
local instance embeddedTransferPresentationAlgebra : Algebra L F :=
  (η).toRingHom.toAlgebra

/-- The presentation algebra agrees with the original base-field algebra. -/
local instance embeddedTransferPresentationTower : IsScalarTower K L F :=
  IsScalarTower.of_algebraMap_eq (fun x => ((η).commutes x).symm)

/-- The ambient closure receives the actual embedded upper-field action. -/
@[instance_reducible]
def embeddedTransferClosureAlgebra : Algebra L (SeparableClosure K) :=
  i.toRingHom.toAlgebra

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The embedding preserves the base-field algebra on the ambient closure. -/
theorem embeddedTransferClosureTower :
    let _ : Algebra L (SeparableClosure K) := embeddedTransferClosureAlgebra K L i
    IsScalarTower K L (SeparableClosure K) := by
  intro closureAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun x => (i.commutes x).symm)

/-- The fixed-field inclusion respects the embedded upper-field action. -/
theorem embeddedTransferPresentationClosureTower :
    let _ : Algebra L (SeparableClosure K) := embeddedTransferClosureAlgebra K L i
    IsScalarTower L F (SeparableClosure K) := by
  intro closureAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- Extend the presentation algebra to its canonical separable closure. -/
local instance embeddedTransferNativePresentationAlgebra :
    Algebra L (SeparableClosure F) :=
  ((algebraMap F (SeparableClosure F)).comp (η).toRingHom).toAlgebra

/-- The native presentation closure uses the same upper-field action. -/
local instance embeddedTransferNativePresentationTower :
    IsScalarTower L F (SeparableClosure F) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The fixed-field presentation is linear for its transported upper-field algebra. -/
def embeddedTransferPresentationEquiv : L ≃ₐ[L] F :=
  { (η).toRingEquiv with commutes' := fun _ => rfl }

/-- The degree-one presentation is finite over the original upper field. -/
local instance embeddedTransferPresentationFinite : FiniteDimensional L F :=
  (embeddedTransferPresentationEquiv K L i).toLinearEquiv.finiteDimensional

/-- The degree-one presentation is Galois over the original upper field. -/
local instance embeddedTransferPresentationGalois : IsGalois L F :=
  IsGalois.of_algEquiv (embeddedTransferPresentationEquiv K L i)

/-- The actual fixed-field presentation has degree one over the upper field. -/
theorem embeddedTransferPresentation_finrank : Module.finrank L F = 1 :=
  Module.finrank_of_bijective_algebraMap (η).bijective

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The ambient native closure is also a separable closure of the embedded field. -/
theorem embeddedTransferIsSepClosure :
    let _ : Algebra L (SeparableClosure K) := embeddedTransferClosureAlgebra K L i
    IsSepClosure L (SeparableClosure K) := by
  intro closureAlgebra
  have : IsScalarTower K L (SeparableClosure K) := embeddedTransferClosureTower K L i
  exact ⟨inferInstance,
    Algebra.isSeparable_tower_top_of_isSeparable K L (SeparableClosure K)⟩

/-- The actual native upper closure compared with the ambient closure
through the original embedded field algebra. -/
def embeddedTransferClosureEquiv :
    let _ : Algebra L (SeparableClosure K) := embeddedTransferClosureAlgebra K L i
    SeparableClosure L ≃ₐ[L] SeparableClosure K := by
  intro closureAlgebra
  have : IsSepClosure L (SeparableClosure K) := embeddedTransferIsSepClosure K L i
  exact IsSepClosure.equiv L (SeparableClosure L) (SeparableClosure K)

/-- Compare the two native closures through the actual fixed-field presentation. -/
def embeddedTransferPresentationClosureEquiv :
    SeparableClosure F ≃ₐ[L] SeparableClosure L := by
  let : Algebra L (SeparableClosure K) := embeddedTransferClosureAlgebra K L i
  have : IsScalarTower L F (SeparableClosure K) :=
    embeddedTransferPresentationClosureTower K L i
  exact ((fixedFieldSeparableClosureEquiv K (SeparableClosure K) H).restrictScalars L).trans
    (embeddedTransferClosureEquiv K L i).symm

/-- The native Galois group of the actual upper field, with values in its
original finite fixing subgroup. All comparison data come from the embedding. -/
def embeddedTransferAbsoluteGaloisEquiv :
    Gal(SeparableClosure L/L) ≃ₜ* (H).field.toSubgroup :=
  presentedFixedFieldAbsoluteGaloisEquiv K L H
    (embeddedTransferPresentation_finrank K L i)
    (fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
    (embeddedTransferPresentationClosureEquiv K L i)

/-- Its actual ambient action is the original native closure conjugation. -/
theorem embeddedTransferAbsoluteGaloisEquiv_apply
    (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K) :
    let : Algebra L (SeparableClosure K) := embeddedTransferClosureAlgebra K L i
    (embeddedTransferAbsoluteGaloisEquiv K L i σ).val x =
      embeddedTransferClosureEquiv K L i
        (σ ((embeddedTransferClosureEquiv K L i).symm x)) := by
  intro closureAlgebra
  rw [embeddedTransferAbsoluteGaloisEquiv,
    presentedFixedFieldAbsoluteGaloisEquiv_apply]
  change
    (fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
      ((fixedFieldSeparableClosureEquiv K (SeparableClosure K) H).symm
        (embeddedTransferClosureEquiv K L i
          (σ ((embeddedTransferClosureEquiv K L i).symm
            ((fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
              ((fixedFieldSeparableClosureEquiv K (SeparableClosure K) H).symm x)))))) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- Actual original transfer between the native absolute abelian groups
of the two original fields, constructed from the actual embedding. -/
def nativeAbsoluteTransferOfEmbedding :
    localAbsoluteAbelianProfinite K →ₜ* localAbsoluteAbelianProfinite L :=
  nativeAbsoluteTransferOfDegreeOnePresentation K L H
    (embeddedTransferPresentation_finrank K L i)
    (fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
    (embeddedTransferPresentationClosureEquiv K L i)

/-- The native embedded transfer is the original subgroup transfer under
the explicitly constructed original Galois comparison. -/
theorem nativeAbsoluteTransferOfEmbedding_comparison :
    have _ : Finite (Gal(SeparableClosure K/K) ⧸ (H).field.toSubgroup) :=
      ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) (H).field (H).finite
    ∀ a : localAbsoluteAbelianProfinite K,
      TopologicalAbelianization.congr (embeddedTransferAbsoluteGaloisEquiv K L i)
          (nativeAbsoluteTransferOfEmbedding K L i a) =
        openNormalTransferTopologicalAbelianization
          (finiteAbstractOpenNormal K (SeparableClosure K) H) a :=
  nativeAbsoluteTransferOfDegreeOnePresentation_comparison K L H
    (embeddedTransferPresentation_finrank K L i)
    (fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
    (embeddedTransferPresentationClosureEquiv K L i)

section Reciprocity

variable (k : Type w) [Field k] [Finite k]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Original native reciprocity of an actual finite Galois extension
carries actual idele inclusion to original transfer. -/
theorem absoluteArtin_baseChange_transferOfEmbedding (c : IdeleClassGroup k K) :
    absoluteArtin k L
        (IdeleClassGroup.baseChange (k := k) (K := K) (L := L) c) =
      nativeAbsoluteTransferOfEmbedding K L i (absoluteArtin k K c) :=
  absoluteArtin_baseChange_presentedTransfer k K L H
    (embeddedTransferPresentation_finrank K L i)
    (fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
    (embeddedTransferPresentationClosureEquiv K L i) c

namespace RayClass

/-- Original native transfer on the reduced ray quotients of the actual
fields, constructed from the explicit finite extension embedding. -/
def nativeRayTransferOfEmbedding (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) →ₜ*
      (localAbsoluteAbelianProfinite L ⧸ artinRaySubgroup (rayModulusBaseChange L m)) :=
  nativeRayTransferOfDegreeOnePresentation k K L H
    (embeddedTransferPresentation_finrank K L i)
    (fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
    (embeddedTransferPresentationClosureEquiv K L i) m hm

/-- The embedded ray transfer retains the literal native absolute transfer. -/
theorem nativeRayTransferOfEmbedding_mk
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (a : localAbsoluteAbelianProfinite K) :
    nativeRayTransferOfEmbedding K L i k m hm
        (QuotientGroup.mk' (artinRaySubgroup m) a) =
      QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange L m))
        (nativeAbsoluteTransferOfEmbedding K L i a) := rfl

/-- The actual restricted-product inclusion square for any actual finite
Galois extension and its original embedding into the lower separable closure. -/
theorem restrictedProductAbsoluteArtin_baseChange_transferOfEmbedding
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (a : RayRestrictedProduct m) :
    restrictedProductAbsoluteArtin (rayModulusBaseChange L m)
        (restrictedRayBaseChange (L := L) m hm a) =
      nativeRayTransferOfEmbedding K L i k m hm (restrictedProductAbsoluteArtin m a) :=
  restrictedProductAbsoluteArtin_baseChange_presentedTransfer k K L H
    (embeddedTransferPresentation_finrank K L i)
    (fixedFieldSeparableClosureEquiv K (SeparableClosure K) H)
    (embeddedTransferPresentationClosureEquiv K L i) m hm a

end RayClass

end Reciprocity

end EmbeddedGroups

end FunctionField
