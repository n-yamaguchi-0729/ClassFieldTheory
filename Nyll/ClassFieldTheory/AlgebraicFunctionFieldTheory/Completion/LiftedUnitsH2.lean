/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormLocalRange
public import Nyll.GaloisCohomology.Kummer.LiftedCyclicUnitsH2BaseChange
public import Nyll.GaloisCohomology.Kummer.LiftedFiniteGaloisTowerUnitsH2

/-!
# Lifted unit H² at the actual completions

The field units, completion embeddings and decomposition restriction maps are unchanged.
Lifted integer coefficients follow the upper-field universe; the original base
field and its completion may live in independent universes.
-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open ClassFieldTower.Cohomology

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Localization of unit H² at the given actual upper place. -/
def liftedCompletionUnitsH2Map (w : Place k L) :
    groupCohomology (liftedGaloisUnitsRep K L) 2 ⟶
      groupCohomology
        (liftedGaloisUnitsRep (w.restrict K).adicCompletion w.adicCompletion) 2 := by
  let : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq
      (fun x => Place.adicCompletionComap_algebraMap_algebraMap K w x)
  exact liftedFiniteGaloisTowerUnitsH2Inflation K L w.adicCompletion ≫
    liftedFiniteGaloisTowerUnitsH2Restriction K (w.restrict K).adicCompletion w.adicCompletion

/-- A local field norm kills the completed image of the associated global cyclic class. -/
theorem liftedCompletionUnitsH2Map_baseUnitClass_eq_zero_of_norm
    [IsCyclic Gal(L/K)] (w : Place k L)
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)
    (a : Kˣ) (x : w.adicCompletion)
    (hx : Algebra.norm (w.restrict K).adicCompletion x =
      algebraMap K (w.restrict K).adicCompletion (a : K)) :
    liftedCompletionUnitsH2Map (K := K) w (liftedCyclicBaseUnitH2Class K L g hg a) = 0 := by
  let : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq
      (fun y => Place.adicCompletionComap_algebraMap_algebraMap K w y)
  exact liftedCyclicBaseUnitH2Class_inflation_restriction_eq_zero_of_norm
    K L (w.restrict K).adicCompletion w.adicCompletion g hg a x hx

/-- A principal idele norm gives a cyclic unit H² class that vanishes at every
actual completed extension. -/
theorem liftedCompletionUnitsH2Map_baseUnitClass_eq_zero_of_principal_norm
    [IsCyclic Gal(L/K)]
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)
    (a : Kˣ) (b : IdeleGroup k L)
    (hb : norm (k := k) (K := K) (L := L) b = principalIdele k K a) (w : Place k L) :
    liftedCompletionUnitsH2Map (K := K) w (liftedCyclicBaseUnitH2Class K L g hg a) = 0 := by
  obtain ⟨x, hx⟩ := exists_localNorm_preimage_of_principal_norm a b hb w
  exact liftedCompletionUnitsH2Map_baseUnitClass_eq_zero_of_norm w g hg a (x : w.adicCompletion)
    (congrArg Units.val hx)

/-- Vanishing at the actual completed extension is equivalent to a local field norm. -/
theorem liftedCompletionUnitsH2Map_baseUnitClass_eq_zero_iff_norm
    [IsCyclic Gal(L/K)] (w : Place k L)
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    liftedCompletionUnitsH2Map (K := K) w (liftedCyclicBaseUnitH2Class K L g hg a) = 0 ↔
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
  exact liftedCyclicBaseUnitH2Class_baseChange_eq_zero_iff_norm
    K L (w.restrict K).adicCompletion w.adicCompletion hinj g hg a

end FunctionField.IdeleGroup
