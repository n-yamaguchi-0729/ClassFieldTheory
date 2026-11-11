/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassField

/-!
# The actual Hilbert class field is independent of constant reindexing

Changing the finite field over which the same function field is regarded
does not change its valuation rings, restriction maps, ramification
indices or residue extensions. The universal unramified and split
property therefore selects the same subfield of the original separable
closure. This comparison retains the original field and its embedding.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FunctionField

open AlgebraicCurve
open scoped AlgebraicCurve.Place

/-- Reindexing the constants preserves the actual Hilbert class field
split at the same place, even when that place has different degrees over
the two finite constant fields. -/
theorem hilbertClassField_forgetConstants
    (k : Type u) (C : Type v) (K : Type w) [Field k] [Finite k] [Field C] [Finite C] [Field K]
    [Algebra k C] [Algebra.IsIntegral k C]
    [Algebra k K] [Algebra C K] [IsScalarTower k C K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc C) K] [IsScalarTower C (RatFunc C) K] [FunctionField C K]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors C K]
    (ε : Place C K) :
    (hilbertClassField k K {ε.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)).val =
      (hilbertClassField C K {ε} (Finset.singleton_nonempty _)).val := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aCΩ : Algebra C (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap C K)).toAlgebra
  let aRkΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  let aRCΩ : Algebra (RatFunc C) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc C) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hCKΩ : IsScalarTower C K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRkKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRCKΩ : IsScalarTower (RatFunc C) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRkΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  have hCRCΩ : IsScalarTower C (RatFunc C) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply C (RatFunc C) K x))
  have hkCΩ : IsScalarTower k C (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k C K x))
  let Hk := hilbertClassField k K {ε.forgetConstants (K := k)}
    (Finset.singleton_nonempty _)
  let HC := hilbertClassField C K {ε} (Finset.singleton_nonempty _)
  have : IsScalarTower k C Hk.val := IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply k C (SeparableClosure K) x)
  have : IsScalarTower k C HC.val := IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply k C (SeparableClosure K) x)
  apply le_antisymm
  · have hspec := hilbertClassField_spec k K {ε.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    apply (le_hilbertClassField_iff C K {ε} (Finset.singleton_nonempty _) Hk).mpr
    refine ⟨fun w => hspec.1 (w.forgetConstants (K := k)), ?_⟩
    intro w hw
    have hrestrict : (w.forgetConstants (K := k)).restrict K =
        (w.restrict K).forgetConstants (K := k) := Place.ext rfl
    have hsplit := hspec.2 (w.forgetConstants (K := k)) (by
      rw [hrestrict, Finset.mem_singleton.mp hw]
      exact Finset.mem_singleton_self _)
    exact hsplit
  · have hspec := hilbertClassField_spec C K {ε} (Finset.singleton_nonempty _)
    apply (le_hilbertClassField_iff k K {ε.forgetConstants (K := k)}
      (Finset.singleton_nonempty _) HC).mpr
    refine ⟨fun w => hspec.1 (w.extendConstants C), ?_⟩
    intro w hw
    have hrestrict : ((w.extendConstants C).restrict K).forgetConstants (K := k) =
        w.restrict K := Place.ext rfl
    have hwC : (w.extendConstants C).restrict K ∈ ({ε} : Finset (Place C K)) := by
      apply Finset.mem_singleton.mpr
      apply Place.forgetConstants_injective (K := k)
      rw [hrestrict]
      exact Finset.mem_singleton.mp hw
    exact hspec.2 (w.extendConstants C) hwC

end FunctionField
