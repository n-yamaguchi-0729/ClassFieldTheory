/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormLocalRange
import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormClass
import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormCriterion
import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormRestriction

/-!
# Unit H² at the actual completions

Localization is the actual inclusion of field units followed by restriction
to completed automorphisms. Local norm preimages kill the localization of
the corresponding cyclic base-unit class.
-/

noncomputable section

open CategoryTheory AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open ClassFieldTower.Cohomology

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Restriction of a completed automorphism through the actual decomposition group. -/
def completionRestrictionHom (w : Place k L) :
    Gal(w.adicCompletion/(w.restrict K).adicCompletion) →* Gal(L/K) :=
  (decompositionGroup (K := K) w).subtype.comp
    (decompositionCompletionEquiv (K := K) w).symm.toMonoidHom

/-- A completed automorphism is determined by its restriction to the original field. -/
theorem completionRestrictionHom_injective (w : Place k L) :
    Function.Injective (completionRestrictionHom (K := K) w) :=
  Subtype.val_injective.comp (decompositionCompletionEquiv (K := K) w).symm.injective

/-- The actual restriction agrees with the automorphism on the included original field. -/
theorem completionRestrictionHom_algebraMap (w : Place k L)
    (σ : Gal(w.adicCompletion/(w.restrict K).adicCompletion)) (x : L) :
    algebraMap L w.adicCompletion (completionRestrictionHom (K := K) w σ x) =
      σ (algebraMap L w.adicCompletion x) := by
  have h := decompositionCompletionEquiv_algebraMap (K := K) w
    ((decompositionCompletionEquiv (K := K) w).symm σ) x
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- Localization of unit H² at the given actual upper place. -/
def completionUnitsH2Map (w : Place k L) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology
        (Rep.ofAlgebraAutOnUnits (w.restrict K).adicCompletion w.adicCompletion) 2 := by
  let : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq
      (fun x => Place.adicCompletionComap_algebraMap_algebraMap K w x)
  exact finiteGaloisTowerUnitsH2Inflation K L w.adicCompletion ≫
    finiteGaloisTowerUnitsH2Restriction K (w.restrict K).adicCompletion w.adicCompletion

/-- A local field norm kills the completed image of the associated global cyclic class. -/
theorem completionUnitsH2Map_baseUnitClass_eq_zero_of_norm
    [IsCyclic Gal(L/K)] (w : Place k L)
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)
    (a : Kˣ) (x : w.adicCompletion)
    (hx : Algebra.norm (w.restrict K).adicCompletion x =
      algebraMap K (w.restrict K).adicCompletion (a : K)) :
    completionUnitsH2Map (K := K) w (finiteCyclicBaseUnitH2Class K L g hg a) = 0 := by
  let : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq
      (fun y => Place.adicCompletionComap_algebraMap_algebraMap K w y)
  exact finiteCyclicBaseUnitH2Class_inflation_restriction_eq_zero_of_norm
    K L (w.restrict K).adicCompletion w.adicCompletion g hg a x hx

/-- A principal idele norm gives a cyclic unit H² class that vanishes at every
actual completed extension. -/
theorem completionUnitsH2Map_baseUnitClass_eq_zero_of_principal_norm
    [IsCyclic Gal(L/K)]
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)
    (a : Kˣ) (b : IdeleGroup k L)
    (hb : norm (k := k) (K := K) (L := L) b = principalIdele k K a) (w : Place k L) :
    completionUnitsH2Map (K := K) w (finiteCyclicBaseUnitH2Class K L g hg a) = 0 := by
  obtain ⟨x, hx⟩ := exists_localNorm_preimage_of_principal_norm a b hb w
  exact completionUnitsH2Map_baseUnitClass_eq_zero_of_norm w g hg a (x : w.adicCompletion)
    (congrArg Units.val hx)

/-- Vanishing at the actual completed extension is equivalent to a local field norm. -/
theorem completionUnitsH2Map_baseUnitClass_eq_zero_iff_norm
    [IsCyclic Gal(L/K)] (w : Place k L)
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    completionUnitsH2Map (K := K) w (finiteCyclicBaseUnitH2Class K L g hg a) = 0 ↔
      ∃ x : w.adicCompletion, Algebra.norm (w.restrict K).adicCompletion x =
        algebraMap K (w.restrict K).adicCompletion (a : K) := by
  let : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq
      (fun y => Place.adicCompletionComap_algebraMap_algebraMap K w y)
  let f : Gal(w.adicCompletion/(w.restrict K).adicCompletion) →* Gal(L/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := w.adicCompletion) L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hf : f = completionRestrictionHom (K := K) w := by
    ext σ x
    apply (algebraMap L w.adicCompletion).injective
    exact ((σ.restrictScalars K).restrictNormal_commutes L x).trans
      (completionRestrictionHom_algebraMap (K := K) w σ x).symm
  have hinj : Function.Injective f := hf ▸ completionRestrictionHom_injective (K := K) w
  exact finiteCyclicBaseUnitH2Class_baseChange_eq_zero_iff_norm
    K L (w.restrict K).adicCompletion w.adicCompletion hinj g hg a

end FunctionField.IdeleGroup
