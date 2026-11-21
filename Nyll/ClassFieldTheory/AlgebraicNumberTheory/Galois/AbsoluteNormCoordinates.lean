/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.EmbeddedAbsoluteRestriction
public import Nyll.GaloisCohomology.Topology.SeparableGaloisMap

/-!
# Native absolute Galois maps and their finite coordinates

Pulling back an embedded finite restriction along the original cross-closure
Galois map produces an actual finite abelian field and an equivariant embedding.
No reciprocity construction or separability of the base extension is required.
-/

@[expose] public section

noncomputable section

universe v w x

namespace FunctionField

open LocalClassFieldTheory ProCGroups.Abelian

section GaloisMaps

variable {K : Type v} {F : Type w} [Field K] [Field F]

/-- The original continuous cross-closure Galois map on the native absolute
topological abelianizations. It is constructed without reciprocity. -/
noncomputable def nativeAbsoluteAbelianMap (f : K →+* F) :
    localAbsoluteAbelianProfinite F →ₜ* localAbsoluteAbelianProfinite K :=
  TopologicalAbelianization.map (Field.absoluteGaloisGroup.separableMap f)

/-- On representatives, the native map is the actual separable Galois map. -/
theorem nativeAbsoluteAbelianMap_mk (f : K →+* F) (σ : Gal(SeparableClosure F/F)) :
    nativeAbsoluteAbelianMap f (QuotientGroup.mk σ : localAbsoluteAbelianProfinite F) =
      (QuotientGroup.mk (Field.absoluteGaloisGroup.separableMap f σ) :
        localAbsoluteAbelianProfinite K) := rfl

end GaloisMaps

section FiniteCoordinate

variable (K : Type v) (F : Type w) (E : Type x)
    [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (i : E →ₐ[K] SeparableClosure K)

/-- The open kernel of the pulled-back finite restriction. -/
noncomputable def normCoordinateKernel :
    OpenNormalSubgroup (localAbsoluteAbelianProfinite F) where
  toOpenSubgroup :=
    { toSubgroup := ((absoluteRestrictionOfEmbedding K E i).comp
        (nativeAbsoluteAbelianMap (algebraMap K F))).toMonoidHom.ker
      isOpen' := (isOpen_discrete {1}).preimage
        ((absoluteRestrictionOfEmbedding K E i).comp
          (nativeAbsoluteAbelianMap (algebraMap K F))).continuous_toFun }
  isNormal' := by infer_instance

/-- The finite abelian field cut out by the pulled-back restriction kernel. -/
noncomputable abbrev normCoordinateField :=
  absoluteFiniteQuotientField F (normCoordinateKernel K F E i)

/-- The original lower embedding lands in the actual field fixed by the
kernel of its pulled-back finite Galois restriction. -/
noncomputable def normCoordinateEmbedding : E →+* normCoordinateField K F E i :=
  ((Field.absoluteGaloisGroup.separableClosureLift (algebraMap K F)).comp i.toRingHom).codRestrict
    (normCoordinateField K F E i) (by
      intro a
      apply (IntermediateField.mem_fixedField_iff _ _).mpr
      intro σ hσ
      have hr : embeddedFiniteRestriction K E i
          (Field.absoluteGaloisGroup.separableMap (algebraMap K F) σ) = 1 := hσ
      have hfix := embeddedFiniteRestriction_commutes K E i
        (Field.absoluteGaloisGroup.separableMap (algebraMap K F) σ) a
      rw [hr] at hfix
      change i a = Field.absoluteGaloisGroup.separableMap (algebraMap K F) σ (i a) at hfix
      exact (Field.absoluteGaloisGroup.separableMap_commutes (algebraMap K F) σ (i a)).symm.trans
        (congrArg (Field.absoluteGaloisGroup.separableClosureLift (algebraMap K F)) hfix.symm))

/-- The coordinate embedding lies over the original base-field embedding. -/
theorem normCoordinateEmbedding_algebraMap (a : K) :
    normCoordinateEmbedding K F E i (algebraMap K E a) =
      algebraMap F (normCoordinateField K F E i) (algebraMap K F a) := by
  apply Subtype.ext
  change Field.absoluteGaloisGroup.separableClosureLift (algebraMap K F)
      (i (algebraMap K E a)) = _
  rw [i.commutes]
  exact Field.absoluteGaloisGroup.separableClosureLift_algebraMap (algebraMap K F) a

/-- The coordinate embedding preserves the specified absolute Galois action. -/
theorem normCoordinateEmbedding_restrict
    (σ : Gal(SeparableClosure F/F)) (a : E) :
    normCoordinateEmbedding K F E i
        (embeddedFiniteRestriction K E i
          (Field.absoluteGaloisGroup.separableMap (algebraMap K F) σ) a) =
      AlgEquiv.restrictNormalHom (normCoordinateField K F E i) σ
        (normCoordinateEmbedding K F E i a) := by
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply]
  change Field.absoluteGaloisGroup.separableClosureLift (algebraMap K F)
      (i (embeddedFiniteRestriction K E i
        (Field.absoluteGaloisGroup.separableMap (algebraMap K F) σ) a)) =
    σ (Field.absoluteGaloisGroup.separableClosureLift (algebraMap K F) (i a))
  rw [embeddedFiniteRestriction_commutes]
  exact Field.absoluteGaloisGroup.separableMap_commutes (algebraMap K F) σ (i a)

end FiniteCoordinate

end FunctionField
