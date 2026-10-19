/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.PrimePowerDescent
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitLocalPowerIndex
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitPowerIndex

/-!
# Localization of S-unit p-power classes

In characteristic p a single completion detects global pth powers.
Saturation of S-units therefore makes localization injective on their
p-power quotient. The cardinality is supplied by the shared Herbrand
calculation.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField.SUnits

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (p : ℕ) [Fact p.Prime] [CharP K p]

/-- A completed pth root of an S-unit gives an actual S-unit root. -/
theorem mem_primePowers_of_completion_power (S : Finset (Place k K))
    (v : Place k K) (a : units k K S) (x : v.adicCompletionˣ)
    (hx : (x : v.adicCompletion) ^ p = algebraMap K v.adicCompletion (a.val : K)) :
    a ∈ (powMonoidHom (α := units k K S) p).range := by
  obtain ⟨b, hb⟩ := exists_pow_eq_of_completion_pow_eq v p (a.val : K) x hx
  have hbne : b ≠ 0 := by
    intro hzero
    have ha := hb
    rw [hzero, zero_pow (Fact.out : p.Prime).ne_zero] at ha
    exact a.val.ne_zero ha.symm
  let u : Kˣ := Units.mk0 b hbne
  have hupow : u ^ p = a.val := Units.ext hb
  have huS : u ∈ units k K S :=
    mem_units_of_pow_mem S p (Fact.out : p.Prime).ne_zero u
      (hupow.symm ▸ a.property)
  exact ⟨⟨u, huS⟩, Subtype.ext hupow⟩

/-- For nonempty S, localization kills exactly the actual S-unit pth powers.
No S-idele surjectivity or roots-of-unity hypothesis is needed. -/
theorem localPrimePowerClassMap_ker (S : Finset (Place k K)) (hS : S.Nonempty) :
    (localPowerClassMap (k := k) (K := K) ⟨p, (Fact.out : p.Prime).pos⟩ S).ker =
      (powMonoidHom (α := units k K S) p).range := by
  apply Subgroup.ext
  intro b
  constructor
  · intro hb
    obtain ⟨v, hv⟩ := hS
    have hz := congrFun hb (⟨v, hv⟩ : S)
    change QuotientGroup.mk' (powMonoidHom (α := v.adicCompletionˣ) p).range
      (Units.map (algebraMap K v.adicCompletion).toMonoidHom b.val) = 1 at hz
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff _).mp hz
    exact mem_primePowers_of_completion_power p S v b x (congrArg Units.val hx)
  · rintro ⟨a, rfl⟩
    apply funext
    intro v
    change QuotientGroup.mk' (powMonoidHom (α := v.val.adicCompletionˣ) p).range
      (Units.map (algebraMap K v.val.adicCompletion).toMonoidHom (a.val ^ p)) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨Units.map (algebraMap K v.val.adicCompletion).toMonoidHom a.val,
      (map_pow (Units.map (algebraMap K v.val.adicCompletion).toMonoidHom) a.val p).symm⟩

/-- The diagonal image of S-units in local p-power classes has precisely
p^(S.card - 1) elements. -/
theorem card_localPrimePowerClassMap_range [HasPrincipalDivisors k K]
    (S : Finset (Place k K)) (hS : S.Nonempty) :
    Nat.card (MonoidHom.range (G := units k K S)
      (N := localPowerClassProduct ⟨p, (Fact.out : p.Prime).pos⟩ S)
      (localPowerClassMap (k := k) (K := K)
        ⟨p, (Fact.out : p.Prime).pos⟩ S)) = p ^ (S.card - 1) := by
  rw [← Subgroup.index_ker, localPrimePowerClassMap_ker p S hS]
  exact card_primePowerQuotient S hS p

end FunctionField.SUnits
