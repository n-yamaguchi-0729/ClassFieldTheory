/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddedAbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalFiniteNormSquare
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteReciprocity
public import Nyll.GaloisCohomology.Topology.SeparableGaloisMap

/-!
# Absolute and completed norm reciprocity for the original Galois map

The native map is the topological abelianization of the existing continuous
cross-closure Galois map. For each finite lower restriction, its pulled-back
kernel cuts out an actual finite abelian upper field. The chosen closure
embedding lands in that field, so the finite norm square applies to the
literal restrictions. Completion then follows by density.

The norm used here is the arbitrary finite-extension norm. No separability
hypothesis is imposed on the base extension.
-/

@[expose] public section

noncomputable section

universe u v w x y

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

private noncomputable def normCoordinateKernel :
    OpenNormalSubgroup (localAbsoluteAbelianProfinite F) where
  toOpenSubgroup :=
    { toSubgroup := ((absoluteRestrictionOfEmbedding K E i).comp
        (nativeAbsoluteAbelianMap (algebraMap K F))).toMonoidHom.ker
      isOpen' := (isOpen_discrete {1}).preimage
        ((absoluteRestrictionOfEmbedding K E i).comp
          (nativeAbsoluteAbelianMap (algebraMap K F))).continuous_toFun }
  isNormal' := by infer_instance

private noncomputable abbrev normCoordinateField :=
  absoluteFiniteQuotientField F (normCoordinateKernel K F E i)

/-- The original lower embedding lands in the actual field fixed by the
kernel of its pulled-back finite Galois restriction. -/
private noncomputable def normCoordinateEmbedding : E →+* normCoordinateField K F E i :=
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

private theorem normCoordinateEmbedding_algebraMap (a : K) :
    normCoordinateEmbedding K F E i (algebraMap K E a) =
      algebraMap F (normCoordinateField K F E i) (algebraMap K F a) := by
  apply Subtype.ext
  change Field.absoluteGaloisGroup.separableClosureLift (algebraMap K F)
      (i (algebraMap K E a)) = _
  rw [i.commutes]
  exact Field.absoluteGaloisGroup.separableClosureLift_algebraMap (algebraMap K F) a

private theorem normCoordinateEmbedding_restrict
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

variable (k : Type u) [Field k] [Finite k]
    [Algebra k K] [Algebra k F] [Algebra k E]
    [IsScalarTower k K F] [IsScalarTower k K E]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional K F]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k F]
    [AlgebraicCurve.HasPrincipalDivisors k E]

/-- Every actual finite embedded restriction of the native absolute Galois
map gives the original finite Artin value of the finite norm. -/
theorem absoluteArtin_finiteNorm_restrictionOfEmbedding (c : IdeleClassGroup k F) :
    absoluteRestrictionOfEmbedding K E i
        (nativeAbsoluteAbelianMap (algebraMap K F) (absoluteArtin k F c)) =
      abelianFiniteArtin k K E (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F) c) := by
  let akΩ : Algebra k (SeparableClosure F) :=
    ((algebraMap F (SeparableClosure F)).comp (algebraMap k F)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure F) :=
    ((algebraMap F (SeparableClosure F)).comp (algebraMap (RatFunc k) F)).toAlgebra
  have hkFΩ : IsScalarTower k F (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRFΩ : IsScalarTower (RatFunc k) F (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun a => congrArg (algebraMap F (SeparableClosure F))
      (IsScalarTower.algebraMap_apply k (RatFunc k) F a))
  let T := normCoordinateField K F E i
  let j : E →+* T := normCoordinateEmbedding K F E i
  let aKT : Algebra K T := ((algebraMap F T).comp (algebraMap K F)).toAlgebra
  let aET : Algebra E T := j.toAlgebra
  have hKFT : IsScalarTower K F T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKET : IsScalarTower K E T :=
    IsScalarTower.of_algebraMap_eq (fun a => (normCoordinateEmbedding_algebraMap K F E i a).symm)
  have hkKT : IsScalarTower k K T :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (IsScalarTower.algebraMap_apply k F T a).trans
        (congrArg (algebraMap F T) (IsScalarTower.algebraMap_apply k K F a)))
  have hkET : IsScalarTower k E T :=
    @IsScalarTower.to₁₃₄ k K E T _ _ _ _ _ _ aKT.toModule.toMulAction
      (inferInstance : IsScalarTower k K E) hkKT hKET
  have hcoordinate (a : localAbsoluteAbelianProfinite F) :
      absoluteRestrictionOfEmbedding K E i (nativeAbsoluteAbelianMap (algebraMap K F) a) =
        AlgEquiv.restrictNormalHom E ((absoluteAbelianRestriction F T a).restrictScalars K) := by
    refine QuotientGroup.induction_on a ?_
    intro σ
    rw [nativeAbsoluteAbelianMap_mk, absoluteRestrictionOfEmbedding_mk,
      absoluteAbelianRestriction_mk]
    apply AlgEquiv.ext
    intro x
    apply j.injective
    exact (normCoordinateEmbedding_restrict K F E i σ x).trans
      ((AlgEquiv.restrictNormalHom T σ).restrictScalars K |>.restrictNormal_commutes E x).symm
  rw [hcoordinate, absoluteArtin_restriction k F T c]
  exact abelianFiniteArtin_finiteNorm_restrictNormal (K := K) (F := F) (L := E) (M := T) c

end FiniteCoordinate

section Reciprocity

variable (k : Type u) (K : Type v) (F : Type w)
    [Field k] [Finite k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional K F]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k F]

/-- The absolute norm square uses the original cross-closure Galois map and
the original finite norm, including inseparable finite extensions. -/
theorem absoluteArtin_finiteNorm (c : IdeleClassGroup k F) :
    nativeAbsoluteAbelianMap (algebraMap K F) (absoluteArtin k F c) =
      absoluteArtin k K (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F) c) := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun a => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K a))
  apply ProfiniteGrp.toLimit_injective (localAbsoluteAbelianProfinite K)
  apply Subtype.ext
  funext N
  apply (absoluteFiniteQuotientEquiv K N).injective
  let E := absoluteFiniteQuotientField K N
  have hrestriction (a : localAbsoluteAbelianProfinite K) :
      absoluteFiniteQuotientEquiv K N (QuotientGroup.mk a) =
        absoluteRestrictionOfEmbedding K E E.val a := by
    refine QuotientGroup.induction_on a ?_
    intro σ
    rw [absoluteFiniteQuotientEquiv_mk_mk, absoluteRestrictionOfEmbedding_mk]
    apply AlgEquiv.ext
    intro x
    apply E.val.injective
    exact (AlgEquiv.restrictNormal_commutes σ E x).trans
      (embeddedFiniteRestriction_commutes K E E.val σ x).symm
  change absoluteFiniteQuotientEquiv K N
      (QuotientGroup.mk (nativeAbsoluteAbelianMap (algebraMap K F) (absoluteArtin k F c))) =
    absoluteFiniteQuotientEquiv K N
      (QuotientGroup.mk (absoluteArtin k K
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F) c)))
  rw [hrestriction, hrestriction,
    absoluteArtin_finiteNorm_restrictionOfEmbedding K F E E.val k c,
    absoluteArtin_restrictionOfEmbedding k K E E.val]

/-- On separable extensions the same square uses the previously defined
separable class norm, with no change to the native Galois map. -/
theorem absoluteArtin_norm [Algebra.IsSeparable K F] (c : IdeleClassGroup k F) :
    nativeAbsoluteAbelianMap (algebraMap K F) (absoluteArtin k F c) =
      absoluteArtin k K (IdeleClassGroup.norm (k := k) (K := K) (L := F) c) := by
  rw [← IdeleClassGroup.finiteNorm_eq_norm]
  exact absoluteArtin_finiteNorm k K F c

/-- Completion of the actual norm intertwines profinite reciprocity with
the independently constructed continuous Galois restriction. -/
theorem profiniteReciprocity_finiteNorm :
    (nativeAbsoluteAbelianMap (algebraMap K F)).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k F)) =
      (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k K)).comp
        (topologicalProfiniteCompletionMapHom
          (IdeleClassGroup.finiteNormContinuous (k := k) (K := K) (L := F))) := by
  let left := (nativeAbsoluteAbelianMap (algebraMap K F)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k F))
  let right := (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k K)).comp
    (topologicalProfiniteCompletionMapHom
      (IdeleClassGroup.finiteNormContinuous (k := k) (K := K) (L := F)))
  have heq := (topologicalProfiniteCompletionMap_denseRange (IdeleClassGroup k F)).equalizer
    left.continuous_toFun right.continuous_toFun (show
      (fun c => left (topologicalProfiniteCompletionMap (IdeleClassGroup k F) c)) =
        (fun c => right (topologicalProfiniteCompletionMap (IdeleClassGroup k F) c)) from by
      funext c
      change nativeAbsoluteAbelianMap (algebraMap K F)
          (profiniteReciprocity k F
            (topologicalProfiniteCompletionMap (IdeleClassGroup k F) c)) =
        profiniteReciprocity k K
          (topologicalProfiniteCompletionMapHom
            (IdeleClassGroup.finiteNormContinuous (k := k) (K := K) (L := F))
            (topologicalProfiniteCompletionMap (IdeleClassGroup k F) c))
      rw [topologicalProfiniteCompletionMapHom_map,
        profiniteReciprocity_map, profiniteReciprocity_map]
      exact absoluteArtin_finiteNorm k K F c)
  exact ContinuousMonoidHom.ext (fun a => congrFun heq a)

/-- The completed separable norm square, using the existing separable norm
homomorphism with its original topology. -/
theorem profiniteReciprocity_norm [Algebra.IsSeparable K F] :
    (nativeAbsoluteAbelianMap (algebraMap K F)).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k F)) =
      (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k K)).comp
        (topologicalProfiniteCompletionMapHom
          (IdeleClassGroup.normContinuous (k := k) (K := K) (L := F))) := by
  have hnorm : IdeleClassGroup.finiteNormContinuous (k := k) (K := K) (L := F) =
      IdeleClassGroup.normContinuous (k := k) (K := K) (L := F) := by
    apply ContinuousMonoidHom.ext
    intro c
    exact DFunLike.congr_fun
      (IdeleClassGroup.finiteNorm_eq_norm (k := k) (K := K) (L := F)) c
  rw [← hnorm]
  exact profiniteReciprocity_finiteNorm k K F

/-- Every finite projection of the completed norm square is the extension
of the same original finite Artin coordinate. -/
theorem profiniteReciprocity_finiteNorm_finiteProjection
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (a : TopologicalProfiniteCompletion (IdeleClassGroup k F)) :
    (QuotientGroup.mk (nativeAbsoluteAbelianMap (algebraMap K F)
        (profiniteReciprocity k F a)) : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) =
      topologicalProfiniteCompletionLift
        ((localAbsoluteAbelianProfinite K).diagram.obj N)
        (absoluteFiniteArtinCoordinate k K N)
        (topologicalProfiniteCompletionMapHom
          (IdeleClassGroup.finiteNormContinuous (k := k) (K := K) (L := F)) a) := by
  have h := DFunLike.congr_fun (profiniteReciprocity_finiteNorm k K F) a
  change nativeAbsoluteAbelianMap (algebraMap K F) (profiniteReciprocity k F a) =
    profiniteReciprocity k K (topologicalProfiniteCompletionMapHom
      (IdeleClassGroup.finiteNormContinuous (k := k) (K := K) (L := F)) a) at h
  rw [h]
  exact completedArtin_finiteProjection k K N _

section Tower

variable (M : Type y) [Field M] [Algebra k M] [Algebra K M] [Algebra F M]
    [IsScalarTower k K M] [IsScalarTower k F M] [IsScalarTower K F M]
    [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M] [FunctionField k M]
    [FiniteDimensional F M] [AlgebraicCurve.HasPrincipalDivisors k M]

include k in
/-- The actual native Galois maps compose on abelianizations in every finite
function-field tower. The proof compares the original maps on the dense
Artin image and uses the original finite norm tower law. -/
theorem nativeAbsoluteAbelianMap_comp_of_finite :
    (nativeAbsoluteAbelianMap (algebraMap K F)).comp
        (nativeAbsoluteAbelianMap (algebraMap F M)) =
      nativeAbsoluteAbelianMap (algebraMap K M) := by
  have hKM : FiniteDimensional K M := FiniteDimensional.trans K F M
  let left := (nativeAbsoluteAbelianMap (algebraMap K F)).comp
    (nativeAbsoluteAbelianMap (algebraMap F M))
  let right := nativeAbsoluteAbelianMap (algebraMap K M)
  have heq := (absoluteArtin_denseRange k M).equalizer
    left.continuous_toFun right.continuous_toFun (show
      (fun c => left (absoluteArtin k M c)) =
        (fun c => right (absoluteArtin k M c)) from by
      funext c
      change nativeAbsoluteAbelianMap (algebraMap K F)
          (nativeAbsoluteAbelianMap (algebraMap F M) (absoluteArtin k M c)) =
        nativeAbsoluteAbelianMap (algebraMap K M) (absoluteArtin k M c)
      rw [absoluteArtin_finiteNorm k F M, absoluteArtin_finiteNorm k K F,
        absoluteArtin_finiteNorm k K M,
        IdeleClassGroup.finiteNorm_trans (k := k) (K := K) (L := F) (M := M) c])
  exact ContinuousMonoidHom.ext (fun a => congrFun heq a)

end Tower

end Reciprocity

end FunctionField
