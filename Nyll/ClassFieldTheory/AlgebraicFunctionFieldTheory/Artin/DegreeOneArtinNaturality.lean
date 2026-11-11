/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.DegreeOneAbsoluteGalois
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddedAbsoluteRestriction
public import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalFiniteNormSquare
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.DegreeOne
public import Nyll.GaloisCohomology.Topology.GaloisRestrictionScalars
public import Nyll.ProCGroups.Profinite.Basic
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Actual reciprocity under a degree-one change of function field

The finite norm square already compares the original Artin maps on an
arbitrary compatible square of actual fields. When the lower extension
has degree one, its norm is inverse to actual idele inclusion. This gives
the finite base-change formula without replacing either reciprocity map.

The original finite restrictions then prove the native absolute formula.
Its Galois equivalence is scalar restriction followed by conjugation by
the specified separable-closure equivalence, so the field action remains
explicit throughout.
-/

@[expose] public section

universe u v w x

noncomputable section

namespace FunctionField

open AlgebraicCurve LocalClassFieldTheory ProCGroups.Abelian

section FiniteArtin

variable {k : Type u} {K : Type v} {F : Type w} {E : Type x}
  [Field k] [Finite k] [Field K] [Field F] [Field E]
  [Algebra k K] [Algebra k F] [Algebra k E]
  [Algebra K F] [Algebra K E] [Algebra F E]
  [IsScalarTower k K F] [IsScalarTower k K E] [IsScalarTower k F E]
  [IsScalarTower K F E]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  [FiniteDimensional K F] [IsGalois K F]
  [FiniteDimensional K E] [FiniteDimensional F E]
  [IsAbelianGalois K E] [IsAbelianGalois F E]
  [HasPrincipalDivisors k K] [HasPrincipalDivisors k F] [HasPrincipalDivisors k E]

/-- Actual finite Artin maps commute with a degree-one base inclusion.
The proof is the existing arbitrary finite norm square and the actual
degree-one norm/inclusion identity. -/
theorem abelianFiniteArtin_baseChange_of_finrank_one
    (hKF : Module.finrank K F = 1) (c : IdeleClassGroup k K) :
    (abelianFiniteArtin k F E
      (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c)).restrictScalars K =
        abelianFiniteArtin k K E c := by
  have h := abelianFiniteArtin_finiteNorm_restrictNormal
    (k := k) (K := K) (F := F) (L := E) (M := E)
    (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c)
  have hself (σ : Gal(E/F)) :
      AlgEquiv.restrictNormalHom E (σ.restrictScalars K) = σ.restrictScalars K := by
    apply AlgEquiv.ext
    intro x
    exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) E x
  rw [hself, IdeleClassGroup.finiteNorm_eq_norm,
    IdeleClassGroup.norm_baseChange, hKF, pow_one] at h
  exact h

end FiniteArtin

private theorem absoluteAbelianRestriction_finiteQuotient
    (K : Type v) [Field K]
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (x : localAbsoluteAbelianProfinite K) :
    absoluteAbelianRestriction K (absoluteFiniteQuotientField K N) x =
      absoluteFiniteQuotientEquiv K N (QuotientGroup.mk x) := by
  refine QuotientGroup.induction_on x ?_
  intro σ
  rw [absoluteAbelianRestriction_mk, absoluteFiniteQuotientEquiv_mk_mk]

section AbsoluteArtin

variable (k : Type u) (K : Type v) (F : Type w)
  [Field k] [Finite k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  [FiniteDimensional K F] [IsGalois K F]
  [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
  [Algebra K (SeparableClosure F)] [IsScalarTower K F (SeparableClosure F)]
  (hKF : Module.finrank K F = 1)
  (eΩ : SeparableClosure F ≃ₐ[K] SeparableClosure K)

/-- Original native absolute reciprocity commutes with an actual
degree-one field inclusion. Every finite abelian coordinate is compared
by the original finite norm theorem. -/
theorem absoluteArtin_baseChange_of_finrank_one (c : IdeleClassGroup k K) :
    degreeOneAbsoluteAbelianEquiv K F hKF eΩ
        (absoluteArtin k F
          (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c)) =
      absoluteArtin k K c := by
  let aKΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let η : K ≃ₐ[K] F := AlgEquiv.ofBijective (Algebra.ofId K F)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hKF)
  apply inv_mul_eq_one.mp
  apply ProCGroups.ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups
  intro N
  apply QuotientGroup.eq.mp
  apply (absoluteFiniteQuotientEquiv K N).injective
  rw [← absoluteAbelianRestriction_finiteQuotient,
    ← absoluteAbelianRestriction_finiteQuotient]
  let E := absoluteFiniteQuotientField K N
  have hEprincipal : HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  let aFE : Algebra F E := ((algebraMap K E).comp η.symm.toRingHom).toAlgebra
  have hKFE : IsScalarTower K F E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap K E x = algebraMap K E (η.symm (η x))
    rw [η.symm_apply_apply]
  have hkFE : IsScalarTower k F E := IsScalarTower.to₁₃₄ k K F E
  have hFE : FiniteDimensional F E := FiniteDimensional.right K F E
  have hFEab : IsAbelianGalois F E := IsAbelianGalois.tower_top K F E
  let i : E →ₐ[F] SeparableClosure F :=
    { toRingHom := eΩ.symm.toRingHom.comp E.val.toRingHom
      commutes' := fun a => by
        change eΩ.symm (algebraMap K (SeparableClosure K) (η.symm a)) =
          algebraMap F (SeparableClosure F) a
        rw [eΩ.symm.commutes,
          IsScalarTower.algebraMap_apply K F (SeparableClosure F)]
        exact congrArg (algebraMap F (SeparableClosure F)) (η.apply_symm_apply a) }
  have hcoordinate (z : localAbsoluteAbelianProfinite F) :
      absoluteAbelianRestriction K E (degreeOneAbsoluteAbelianEquiv K F hKF eΩ z) =
        (absoluteRestrictionOfEmbedding F E i z).restrictScalars K := by
    refine QuotientGroup.induction_on z ?_
    intro σ
    rw [degreeOneAbsoluteAbelianEquiv_mk, absoluteAbelianRestriction_mk,
      absoluteRestrictionOfEmbedding_mk]
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E (SeparableClosure K)).injective
    calc
      algebraMap E (SeparableClosure K)
          ((AlgEquiv.restrictNormalHom E
            (degreeOneAbsoluteGaloisEquiv K F hKF eΩ σ)) x) =
          eΩ (σ (eΩ.symm (algebraMap E (SeparableClosure K) x))) :=
        AlgEquiv.restrictNormal_commutes
          (degreeOneAbsoluteGaloisEquiv K F hKF eΩ σ) E x
      _ = eΩ (i (embeddedFiniteRestriction F E i σ x)) :=
        congrArg eΩ (embeddedFiniteRestriction_commutes F E i σ x).symm
      _ = algebraMap E (SeparableClosure K)
          ((embeddedFiniteRestriction F E i σ).restrictScalars K x) :=
        eΩ.apply_symm_apply _
  rw [hcoordinate, absoluteArtin_restrictionOfEmbedding,
    absoluteArtin_restriction]
  exact abelianFiniteArtin_baseChange_of_finrank_one hKF c

end AbsoluteArtin

end FunctionField
