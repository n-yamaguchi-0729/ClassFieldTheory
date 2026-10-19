/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.CyclicStageNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.LocalUnitsH2
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The Hasse norm theorem for finite cyclic function-field extensions

Embed the given extension into a separable closure. The resulting finite
Galois stage satisfies the proved Hasse norm theorem. Idele inclusion into
this isomorphic stage has relative degree one, so norm transitivity transfers
the theorem to the original fields and their actual norm maps.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.NormObstruction

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Every principal idele norm in a finite cyclic extension is an actual field norm. -/
theorem principalNormSubgroup_eq_fieldNormSubgroup [IsCyclic Gal(L/K)] :
    principalNormSubgroup (k := k) (K := K) (L := L) =
      fieldNormSubgroup (K := K) (L := L) := by
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) Ω :=
    ((algebraMap K Ω).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) Ω := IsScalarTower.of_algebraMap_eq (fun x =>
    congrArg (algebraMap K Ω) (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let i : L →ₐ[K] Ω := IsSepClosed.lift
  let E : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := i.fieldRange
      finiteDimensional := i.equivFieldRange.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv i.equivFieldRange }
  let e : L ≃ₐ[K] E := i.equivFieldRange
  have hKEfin : FiniteDimensional K E := E.finiteDimensional
  have hKEgal : IsGalois K E := E.isGalois
  have hEcurve : IsCurveOver k E :=
    IdeleClassGroup.FiniteExtensionSystem.stageIsCurveOver E
  let aLE : Algebra L E := e.toAlgHom.toAlgebra
  have hKLE : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  have hkLE : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply k K E, IsScalarTower.algebraMap_apply k K L,
      ← IsScalarTower.algebraMap_apply K L E])
  let eL : L ≃ₐ[L] E := { e.toRingEquiv with commutes' := fun _ => rfl }
  have hLEfin : FiniteDimensional L E := eL.toLinearEquiv.finiteDimensional
  have hLEgal : IsGalois L E := IsGalois.of_algEquiv eL
  have hdegree : Module.finrank L E = 1 :=
    Module.finrank_of_bijective_algebraMap e.bijective
  have hcyc : IsCyclic Gal(E/K) :=
    isCyclic_of_surjective (AlgEquiv.autCongr e) (AlgEquiv.autCongr e).surjective
  apply le_antisymm
  · intro a ha
    obtain ⟨b, hb⟩ := ha
    let bE := IdeleGroup.baseChange (k := k) (K := L) (L := E) b
    have hbE : IdeleGroup.norm (k := k) (K := L) (L := E) bE = b := by
      rw [IdeleGroup.norm_baseChange, hdegree, pow_one]
    have hprincipal : a ∈ principalNormSubgroup (k := k) (K := K) (L := E) := by
      refine ⟨bE, ?_⟩
      exact (IdeleGroup.norm_trans (k := k) (K := K) (L := L) bE).symm.trans
        ((congrArg (IdeleGroup.norm (k := k) (K := K) (L := L)) hbE).trans hb)
    obtain ⟨x, hx⟩ :=
      (FunctionField.principalNormSubgroup_eq_fieldNormSubgroup_cyclicStage k K Ω E).le hprincipal
    refine ⟨Units.map (Algebra.norm L : E →* L) x, Units.ext ?_⟩
    change Algebra.norm K (Algebra.norm L (x : E)) = (a : K)
    rw [Algebra.norm_norm]
    exact congrArg Units.val hx
  · exact fieldNormSubgroup_le_principalNormSubgroup

open ClassFieldTower.Cohomology

/-- A nonzero element is a global norm exactly when it is a norm at every actual completion. -/
theorem exists_norm_iff_forall_completion_norm [IsCyclic Gal(L/K)]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L] (a : Kˣ) :
    (∃ x : L, Algebra.norm K x = (a : K)) ↔
      ∀ w : Place k L, ∃ x : w.adicCompletion,
        Algebra.norm (w.restrict K).adicCompletion x =
          algebraMap K (w.restrict K).adicCompletion (a : K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  constructor
  · intro ha w
    have hzero := (finiteCyclicBaseUnitH2Class_eq_zero_iff_norm K L g hg a).mpr ha
    apply (IdeleGroup.completionUnitsH2Map_baseUnitClass_eq_zero_iff_norm w g hg a).mp
    rw [hzero, map_zero]
  · intro ha
    have hprincipal := (IdeleGroup.baseUnitH2Class_locally_zero_iff_principal_norm
      (k := k) g hg a).mp (fun w =>
        (IdeleGroup.completionUnitsH2Map_baseUnitClass_eq_zero_iff_norm w g hg a).mpr (ha w))
    obtain ⟨x, hx⟩ :=
      (principalNormSubgroup_eq_fieldNormSubgroup (k := k) (K := K) (L := L)).le hprincipal
    exact ⟨(x : L), congrArg Units.val hx⟩

end FunctionField.NormObstruction
