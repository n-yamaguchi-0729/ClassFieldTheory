/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitLocalPower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitKummerDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PositiveCharacteristicPowerIndex
import Mathlib.GroupTheory.Index

/-!
# The actual image of S-units in local power classes

Local power detection identifies the localization kernel with actual S-unit
powers. The computed S-unit power index gives the image order. The actual
completion power indices then compute its quotient index, equal to the
degree of the S-unit Kummer extension.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.SUnits

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- The product of the actual completed multiplicative power quotients at S. -/
abbrev localPowerClassProduct (n : ℕ+) (S : Finset (Place k K)) :=
  ∀ v : S, v.val.adicCompletionˣ ⧸
    (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range

/-- Localization of actual S-units in the product of completed power quotients. -/
def localPowerClassMap (n : ℕ+) (S : Finset (Place k K)) :
    units k K S →* localPowerClassProduct n S :=
  MonoidHom.pi fun v =>
    (QuotientGroup.mk' (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range).comp
      ((Units.map (algebraMap K v.val.adicCompletion).toMonoidHom).comp
        (units k K S).subtype)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- When S-ideles represent all classes, localization kills exactly S-unit powers. -/
theorem localPowerClassMap_ker (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (S : Finset (Place k K))
    (hS : Function.Surjective (IdeleGroup.sIdeleClass S)) :
    (localPowerClassMap (k := k) (K := K) n S).ker =
      (powMonoidHom (α := units k K S) (n : ℕ)).range := by
  ext b
  constructor
  · intro hb
    have hlocal (v : Place k K) (hv : v ∈ S) : ∃ x : v.adicCompletionˣ,
        (x : v.adicCompletion) ^ (n : ℕ) = algebraMap K v.adicCompletion (b.val : K) := by
      have hvzero := congrFun hb (⟨v, hv⟩ : S)
      change (QuotientGroup.mk' (powMonoidHom (α := v.adicCompletionˣ) (n : ℕ)).range
        (Units.map (algebraMap K v.adicCompletion).toMonoidHom b.val)) = 1 at hvzero
      obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff _).mp hvzero
      exact ⟨x, congrArg Units.val hx⟩
    rw [← nthPowers_subgroupOf_units]
    exact mem_nthPowers_of_local_powers n hn hmu S hS b hlocal
  · rintro ⟨a, rfl⟩
    apply funext
    intro v
    change QuotientGroup.mk' (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range
      (Units.map (algebraMap K v.val.adicCompletion).toMonoidHom (a.val ^ (n : ℕ))) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨Units.map (algebraMap K v.val.adicCompletion).toMonoidHom a.val,
      (map_pow (Units.map (algebraMap K v.val.adicCompletion).toMonoidHom) a.val n).symm⟩

/-- The actual diagonal image has n raised to the number of places elements. -/
theorem card_localPowerClassMap_range (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (S : Finset (Place k K))
    (hSne : S.Nonempty) (hS : Function.Surjective (IdeleGroup.sIdeleClass S)) :
    Nat.card (MonoidHom.range (G := units k K S) (N := localPowerClassProduct n S)
      (localPowerClassMap (k := k) (K := K) n S)) = (n : ℕ) ^ S.card := by
  rw [← Subgroup.index_ker, localPowerClassMap_ker n hn hmu S hS]
  exact card_powerQuotient S hSne n hmu

omit [HasPrincipalDivisors k K] in
/-- A completion contains the base roots of unity and has the actual positive
characteristic, so its power quotient has n squared elements. -/
theorem card_completionPowerQuotient (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (v : Place k K) :
    Nat.card (v.adicCompletionˣ ⧸
      (powMonoidHom (α := v.adicCompletionˣ) (n : ℕ)).range) = (n : ℕ) ^ 2 := by
  let relation : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have hlocal : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  have hKchar : CharP K (ringChar k) := (Algebra.charP_iff k K (ringChar k)).mp inferInstance
  have hVchar : CharP v.adicCompletion (ringChar k) :=
    charP_of_injective_algebraMap (algebraMap K v.adicCompletion).injective (ringChar k)
  have hnV : (((n : ℕ) : v.adicCompletion)) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap K v.adicCompletion)).mpr hn
  obtain ⟨ζ, hζ⟩ := hmu
  have hζV : IsPrimitiveRoot (algebraMap K v.adicCompletion ζ) (n : ℕ) :=
    (isPrimitiveRoot_of_mem_primitiveRoots hζ).map_of_injective
      (algebraMap K v.adicCompletion).injective
  exact LocalFieldTheory.card_nthPowerQuotient_eq_sq_of_positiveCharacteristic
    v.adicCompletion (ringChar k) n hnV
      ⟨algebraMap K v.adicCompletion ζ, (mem_primitiveRoots n.pos).mpr hζV⟩

/-- The quotient of the local product by the actual diagonal S-unit image has
order n raised to the number of places. -/
theorem index_localPowerClassMap_range (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (S : Finset (Place k K))
    (hSne : S.Nonempty) (hS : Function.Surjective (IdeleGroup.sIdeleClass S)) :
    (MonoidHom.range (G := units k K S) (N := localPowerClassProduct n S)
      (localPowerClassMap (k := k) (K := K) n S)).index = (n : ℕ) ^ S.card := by
  have htotal : Nat.card (∀ v : S, v.val.adicCompletionˣ ⧸
      (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range) =
        (n : ℕ) ^ S.card * (n : ℕ) ^ S.card := by
    rw [Nat.card_pi]
    simp only [card_completionPowerQuotient n hn hmu, Finset.prod_const,
      Finset.card_univ, Fintype.card_coe, pow_two, mul_pow]
  have hmul := (MonoidHom.range (G := units k K S) (N := localPowerClassProduct n S)
      (localPowerClassMap (k := k) (K := K) n S)).card_mul_index
  rw [card_localPowerClassMap_range n hn hmu S hSne hS, htotal] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos n.pos S.card) hmul

end FunctionField.SUnits
