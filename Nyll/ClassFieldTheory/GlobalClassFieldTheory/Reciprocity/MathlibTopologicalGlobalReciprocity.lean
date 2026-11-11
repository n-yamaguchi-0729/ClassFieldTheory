/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteAbelianization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel

/-!
# Topological global reciprocity in Mathlib's groups

The existing maximal-abelian Artin isomorphism is transported through the
topological comparison of idèle class groups and the canonical comparison of
absolute Galois abelianizations, on the original carrier in any universe.
The previously specified Small transport and named map are retained.
`MathlibGlobalArtinNaturality` proves their equality with native reciprocity,
actual finite projections, and model independence from pointwise naturality.
-/

@[expose] public section

open scoped NumberField

noncomputable section

universe u

namespace GlobalClassFieldTheory.Reciprocity

/-- The maximal-abelian Artin isomorphism, expressed entirely in Mathlib's
idèle-class and absolute-Galois groups, on the original number-field carrier. -/
noncomputable def mathlibIdeleClassConnectedQuotientEquivAbelianization
    (K : Type u) [Field K] [NumberField K] :
    ClassFieldTheory.IdeleClassConnectedQuotient K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K := by
  let classEquiv : IdeleClassGroup K ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
  let compEquiv := ClassFieldTheory.connectedComponentQuotientCongr classEquiv
  let e₁ : ClassFieldTheory.IdeleClassConnectedQuotient K ≃ₜ*
      ideleClassComponentQuotient K := compEquiv.symm
  let e₂ : ideleClassComponentQuotient K ≃ₜ*
      Gal(maximalAbelianExtension K / K) :=
    ideleClassComponentQuotientEquivMaximalAbelianGalois K
  let e₃ : TopologicalAbelianization Gal(SeparableClosure K / K) ≃ₜ*
      Gal(maximalAbelianExtension K / K) :=
    absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K
  let e₄ : Field.absoluteGaloisGroupAbelianization K ≃ₜ*
      TopologicalAbelianization Gal(SeparableClosure K / K) :=
    absoluteGaloisGroupAbelianizationEquivSeparable K
  exact e₁.trans (e₂.trans (e₃.symm.trans e₄.symm))

open ClassFieldTheory

/-- The existing geometric reciprocity isomorphism transported through the
specified small-field equivalence, on the original number-field carrier. -/
noncomputable def mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse
    (K : Type u) [Field K] [NumberField K] :
    ClassFieldTheory.IdeleClassConnectedQuotient K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K := by
  let : Small.{0} K := numberField_small K
  let S := Shrink.{0} K
  let : NumberField S := numberField_shrink K
  let e : S ≃ₐ[ℚ] K := (Shrink.ringEquiv K).toRatAlgEquiv
  let cS : IdeleClassGroup S ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 S) S :=
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib S
  let cK : IdeleClassGroup K ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
  let c : NumberField.IdeleClassGroup (𝓞 S) S ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    cS.symm.trans ((ideleClassCongrContinuousMulEquiv e).trans cK)
  let q : IdeleClassConnectedQuotient S ≃ₜ*
      IdeleClassConnectedQuotient K :=
    connectedComponentQuotientCongr c
  let g : Field.absoluteGaloisGroupAbelianization S ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
  let r : IdeleClassConnectedQuotient S ≃ₜ*
      Field.absoluteGaloisGroupAbelianization S :=
    GlobalClassFieldTheory.Reciprocity.mathlibIdeleClassConnectedQuotientEquivAbelianization S
  exact q.symm.trans (r.trans g)

/-- The named continuous Artin map on Mathlib's idèle class group. It keeps
the geometric normalization of the existing maximal-abelian construction. -/
noncomputable def mathlibGlobalArtin
    (K : Type u) [Field K] [NumberField K] :
    NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K)).comp
    { toMonoidHom := QuotientGroup.mk'
        (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K))
      continuous_toFun := QuotientGroup.continuous_mk }

/-- Evaluation uses the specified quotient isomorphism on the same class. -/
theorem mathlibGlobalArtin_apply
    (K : Type u) [Field K] [NumberField K]
    (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    mathlibGlobalArtin K c =
      mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K
        (QuotientGroup.mk'
          (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) c) :=
  rfl

/-- The named Artin map is surjective. -/
theorem mathlibGlobalArtin_surjective
    (K : Type u) [Field K] [NumberField K] :
    Function.Surjective (mathlibGlobalArtin K) :=
  (mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K).surjective.comp
    (QuotientGroup.mk'_surjective _)

/-- The kernel is the actual identity component of Mathlib's idèle class group. -/
theorem mathlibGlobalArtin_ker
    (K : Type u) [Field K] [NumberField K] :
    (mathlibGlobalArtin K).toMonoidHom.ker =
      Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K) := by
  ext c
  change (mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K).toMulEquiv
      (QuotientGroup.mk'
        (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) c) = 1 ↔ _
  rw [(mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K).map_eq_one_iff]
  exact QuotientGroup.eq_one_iff c

end GlobalClassFieldTheory.Reciprocity
