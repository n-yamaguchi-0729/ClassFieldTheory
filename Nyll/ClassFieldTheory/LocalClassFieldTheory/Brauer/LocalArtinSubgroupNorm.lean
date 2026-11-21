/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteGaloisArtin

/-! # Finite local Artin and norm from an intermediate field -/

@[expose] public section

noncomputable section

open CategoryTheory FunctionField LocalClassFieldTheory LocalFieldTheory ProCGroups.Abelian
open scoped ValuativeRel
open ClassFieldTower.Martinet.Shafarevich

namespace ClassFieldTheory.Brauer

universe u v w

section Norm

variable (K : Type u) (L : Type v) (F : Type w)
  [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K F] [Algebra.IsSeparable K F]
  (i : L →ₐ[K] SeparableClosure K)

local notation "iF" => (i.comp (IsScalarTower.toAlgHom K F L))

/-- The same original embedding, viewed over the intermediate field in
its chosen separable closure. -/
def localIntermediateUpperEmbedding
    (e : LocalFiniteExtensionClosureEquiv K F iF) : L →ₐ[F] SeparableClosure F := by
  let : Algebra F (SeparableClosure K) := (iF).toRingHom.toAlgebra
  exact
    { toRingHom := e.symm.toRingHom.comp i.toRingHom
      commutes' := fun a => by
        change e.symm (iF a) = algebraMap F (SeparableClosure F) a
        apply e.injective
        exact (e.apply_symm_apply (iF a)).trans (e.commutes a).symm }

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]

/-- Taking the norm from the intermediate field carries the existing Artin
value through inclusion of the actual subgroup on abelianizations. -/
theorem localArtinMapOfEmbedding_norm_restrictScalars
    (e : LocalFiniteExtensionClosureEquiv K F iF) (a : Fˣ) :
    let : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
    let : FiniteDimensional F L := FiniteDimensional.right K F L
    (topologicalAbelianization_finite_equiv K L).symm
        (Universe.localArtinMapOfEmbedding K L i (normUnits K F a)) =
      Group.Abelianization.map (AlgEquiv.restrictScalarsHom K : Gal(L/F) →* Gal(L/K))
        ((topologicalAbelianization_finite_equiv F L).symm
          (Universe.localArtinMapOfEmbedding F L
            (localIntermediateUpperEmbedding K L F i e) a)) := by
  intro hGalois hFinite
  let : Algebra F (SeparableClosure K) := (iF).toRingHom.toAlgebra
  let j := localIntermediateUpperEmbedding K L F i e
  let b := localFiniteExtensionAbsoluteInclusion K F iF e
  rw [Universe.localArtinMapOfEmbedding_toAbelianization,
    Universe.localArtinMapOfEmbedding_toAbelianization,
    ← separableAbsoluteLocalArtinMap_finiteExtension_norm K F iF e]
  generalize separableAbsoluteLocalArtinMap F a = z
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk (Gal(SeparableClosure F/F)) z
  change absoluteAbelianizedRestrictionOfEmbedding K L i
      (TopologicalAbelianization.map b (TopologicalAbelianization.mk _ σ)) = _
  rw [TopologicalAbelianization.map_apply_mk]
  let r := Group.Abelianization.map (AlgEquiv.restrictScalarsHom K : Gal(L/F) →* Gal(L/K))
  change absoluteAbelianizedRestrictionOfEmbedding K L i
      (QuotientGroup.mk (b σ) : localAbsoluteAbelianProfinite K) =
    r (absoluteAbelianizedRestrictionOfEmbedding F L j
      (QuotientGroup.mk σ : localAbsoluteAbelianProfinite F))
  refine (absoluteAbelianizedRestrictionOfEmbedding_mk K L i (b σ)).trans
    (Eq.trans ?_ (congrArg r (absoluteAbelianizedRestrictionOfEmbedding_mk F L j σ)).symm)
  change Group.Abelianization.of (embeddedFiniteRestriction K L i (b σ)) =
    Group.Abelianization.of (AlgEquiv.restrictScalarsHom K (embeddedFiniteRestriction F L j σ))
  apply congrArg Group.Abelianization.of
  apply AlgEquiv.ext
  intro x
  apply i.injective
  calc
    i (embeddedFiniteRestriction K L i (b σ) x) = b σ (i x) :=
      embeddedFiniteRestriction_commutes K L i (b σ) x
    _ = e (σ (e.symm (i x))) := localFiniteExtensionAbsoluteInclusion_apply K F iF e σ (i x)
    _ = e (σ (j x)) := rfl
    _ = e (j (embeddedFiniteRestriction F L j σ x)) :=
      congrArg e (embeddedFiniteRestriction_commutes F L j σ x).symm
    _ = i ((AlgEquiv.restrictScalarsHom K (embeddedFiniteRestriction F L j σ)) x) :=
      e.apply_symm_apply _

end Norm

/-- On a finite abelian stage the original finite Artin coordinate has the
literal value of the abelian Artin map, read in the original group. -/
theorem localArtinMapOfEmbedding_eq_stage_abelian
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [IsAbelianGalois K E]
    (d : L ≃ₐ[K] E) (a : Kˣ) :
    (topologicalAbelianization_finite_equiv K L).symm
        (Universe.localArtinMapOfEmbedding K L (E.toIntermediateField.val.comp d.toAlgHom) a) =
      Group.Abelianization.of ((AlgEquiv.autCongr d).symm (abelianLocalArtinMap K E a)) := by
  let : FiniteDimensional K (↥E.toIntermediateField) := E.finiteDimensional
  let j := E.toIntermediateField.val.comp d.toAlgHom
  rw [Universe.localArtinMapOfEmbedding_toAbelianization,
    ← separableAbsoluteLocalArtinMap_restriction K E.toIntermediateField]
  generalize separableAbsoluteLocalArtinMap K a = z
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk (Gal(SeparableClosure K/K)) z
  change absoluteAbelianizedRestrictionOfEmbedding K L j
      (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
    Group.Abelianization.of ((AlgEquiv.autCongr d).symm (absoluteAbelianRestriction K
      E.toIntermediateField (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K)))
  rw [absoluteAbelianizedRestrictionOfEmbedding_mk K L j σ,
    absoluteAbelianRestriction_mk K E.toIntermediateField σ]
  apply congrArg Group.Abelianization.of
  apply AlgEquiv.ext
  intro x
  apply j.injective
  calc
    j (embeddedFiniteRestriction K L j σ x) = σ (j x) :=
      embeddedFiniteRestriction_commutes K L j σ x
    _ = E.toIntermediateField.val ((AlgEquiv.restrictNormalHom E.toIntermediateField σ) (d x)) :=
      (AlgEquiv.restrictNormal_commutes σ E.toIntermediateField (d x)).symm
    _ = j (((AlgEquiv.autCongr d).symm (AlgEquiv.restrictNormalHom E.toIntermediateField σ)) x) :=
      congrArg E.toIntermediateField.val (d.apply_symm_apply _).symm

end ClassFieldTheory.Brauer
