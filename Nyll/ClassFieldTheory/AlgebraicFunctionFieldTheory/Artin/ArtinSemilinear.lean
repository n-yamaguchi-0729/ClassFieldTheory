/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalFiniteNormSquare
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteBaseChange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality

/-!
# Semilinear naturality of the original finite global Artin map

Compatible equivalences of the base and extension fields identify the
actual Artin maps. The base equivalence is viewed as a degree-one field
extension; the proved finite global norm square and the actual
inclusion-norm identity then give the conjugation formula.
-/

@[expose] public section

noncomputable section

universe u v w x y

namespace FunctionField

open AlgebraicCurve

variable {k : Type u} {K : Type v} {F : Type w} {L : Type x} {M : Type y}
    [Field k] [Finite k]
    [Field K] [Field F] [Field L] [Field M]
    [Algebra k K] [Algebra k F] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra F M] [IsScalarTower k K L] [IsScalarTower k F M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional F M] [IsAbelianGalois F M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
    [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- The actual finite global Artin homomorphism commutes with compatible
field equivalences. The idele map on the right is the original base-change
map for the field embedding defined by the given equivalence. -/
theorem abelianFiniteArtin_algEquiv_conjugation
    (eK : K ≃ₐ[k] F) (eL : L ≃ₐ[k] M)
    (hcomm : ∀ a : K, eL (algebraMap K L a) = algebraMap F M (eK a)) :
    let _ : Algebra K F := eK.toRingHom.toAlgebra
    let _ : IsScalarTower k K F :=
      IsScalarTower.of_algebraMap_eq (fun a => (eK.commutes a).symm)
    let eK' : K ≃ₐ[K] F := { eK.toRingEquiv with commutes' := fun _ => rfl }
    let _ : FiniteDimensional K F :=
      FiniteDimensional.of_surjective eK'.toLinearMap eK'.surjective
    ∀ c : IdeleClassGroup k K,
      LocalClassFieldTheory.semilinearGaloisGroupCongr K F L M
          eK.toRingEquiv eL.toRingEquiv hcomm (abelianFiniteArtin k K L c) =
        abelianFiniteArtin k F M
          (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c) := by
  intro aKF hkKF eK' hKF c
  let aKM : Algebra K M := ((algebraMap F M).comp eK.toRingHom).toAlgebra
  let aLM : Algebra L M := eL.toRingHom.toAlgebra
  have hKFM : IsScalarTower K F M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKLM : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq (fun a => (hcomm a).symm)
  have hkKM : IsScalarTower k K M :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [IsScalarTower.algebraMap_apply k F M]
      exact congrArg (algebraMap F M) (eK.commutes a).symm)
  have hkLM : IsScalarTower k L M :=
    IsScalarTower.of_algebraMap_eq (fun a => (eL.commutes a).symm)
  let conjugation := LocalClassFieldTheory.semilinearGaloisGroupCongr K F L M
    eK.toRingEquiv eL.toRingEquiv hcomm
  let restriction : Gal(M/F) →* Gal(L/K) :=
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
  have hrestriction (τ : Gal(M/F)) : restriction τ = conjugation.symm τ := by
    apply AlgEquiv.ext
    intro a
    apply eL.injective
    have hconjugation : τ (eL a) = eL (conjugation.symm τ a) := by
      have h := LocalClassFieldTheory.semilinearGaloisGroupCongr_apply_equiv
        K F L M eK.toRingEquiv eL.toRingEquiv hcomm (conjugation.symm τ) a
      change conjugation (conjugation.symm τ) (eL a) =
        eL (conjugation.symm τ a) at h
      rw [conjugation.apply_symm_apply] at h
      exact h
    exact (AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L a).trans hconjugation
  have hdegree : Module.finrank K F = 1 := by
    rw [← eK'.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hnorm : IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F)
      (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c) = c := by
    rw [IdeleClassGroup.finiteNorm_baseChange, hdegree, pow_one]
  have hpoint := abelianFiniteArtin_finiteNorm_restrictNormal
    (k := k) (K := K) (F := F) (L := L) (M := M)
      (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c)
  change restriction (abelianFiniteArtin k F M
      (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c)) =
    abelianFiniteArtin k K L (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F)
      (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c)) at hpoint
  rw [hrestriction, hnorm] at hpoint
  exact (congrArg conjugation hpoint).symm.trans (conjugation.apply_symm_apply _)

end FunctionField
