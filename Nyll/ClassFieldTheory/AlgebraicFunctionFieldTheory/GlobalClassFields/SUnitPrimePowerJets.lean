/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitPrimePower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassTopology

/-!
# Finite-depth detection of S-unit characteristic-power classes

The finite S-unit p-power quotient has finitely many representatives.
Closedness of local powers separates those representatives at a finite
principal-unit depth. Local p-power descent then detects the original
global p-power class.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField.SUnits

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]
    (p : ℕ) [Fact p.Prime] [CharP K p]

/-- One completion, at sufficiently large finite depth, detects every S-unit p-class. -/
theorem exists_primePower_jet_detection (S : Finset (Place k K)) (hS : S.Nonempty)
    (v : Place k K) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ n : ℕ, r ≤ n → ∀ a : units k K S,
      (Units.map (algebraMap K v.adicCompletion).toMonoidHom a.val ∈
        (powMonoidHom (α := v.adicCompletionˣ) p).range ⊔
          RayClass.localHigherUnitGroup v n ↔
        a ∈ (powMonoidHom (α := units k K S) p).range) := by
  classical
  let relation : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have hlocal : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  let P : Subgroup (units k K S) := (powMonoidHom (α := units k K S) p).range
  let Q := units k K S ⧸ P
  have hfinite : Finite Q :=
    (finite_card_powerQuotient S hS ⟨p, (Fact.out : p.Prime).pos⟩).1
  let : Fintype Q := Fintype.ofFinite Q
  let f : units k K S →* v.adicCompletionˣ :=
    (Units.map (algebraMap K v.adicCompletion).toMonoidHom).comp
      (units k K S).subtype
  let T : Finset v.adicCompletionˣ := Finset.univ.image (fun q : Q => f q.out)
  obtain ⟨r, hr, hT⟩ :=
    LocalFieldTheory.exists_powerSup_principalUnits_separates_finset
      v.adicCompletion p (Fact.out : p.Prime).ne_zero T
  have hpower (a : units k K S) (ha : a ∈ P) :
      f a ∈ (powMonoidHom (α := v.adicCompletionˣ) p).range := by
    obtain ⟨b, rfl⟩ := ha
    exact ⟨f b, (map_pow f b p).symm⟩
  have hdetect (a : units k K S)
      (ha : f a ∈ (powMonoidHom (α := v.adicCompletionˣ) p).range) : a ∈ P := by
    obtain ⟨x, hx⟩ := ha
    exact mem_primePowers_of_completion_power p S v a x (congrArg Units.val hx)
  let H : Subgroup v.adicCompletionˣ :=
    (powMonoidHom (α := v.adicCompletionˣ) p).range ⊔
      RayClass.localHigherUnitGroup v r
  let fH : units k K S →* v.adicCompletionˣ ⧸ H := (QuotientGroup.mk' H).comp f
  have hker : P ≤ fH.ker := by
    intro a ha
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left (hpower a ha))
  let g : Q →* v.adicCompletionˣ ⧸ H := QuotientGroup.lift P fH hker
  have hseparate (a : units k K S) (ha : f a ∈ H) : a ∈ P := by
    let q : Q := QuotientGroup.mk' P a
    have hga : g q = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    have hout : QuotientGroup.mk' P q.out = q := Quotient.out_eq q
    have hgo : fH q.out = 1 := by
      change g (QuotientGroup.mk' P q.out) = 1
      rw [hout]
      exact hga
    have hmem : f q.out ∈ T := Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
    have hpowerOut := (hT (f q.out) hmem).mp
      ((QuotientGroup.eq_one_iff _).mp hgo)
    have hq : q = 1 := hout.symm.trans
      ((QuotientGroup.eq_one_iff _).mpr (hdetect q.out hpowerOut))
    exact (QuotientGroup.eq_one_iff _).mp hq
  refine ⟨r, hr, fun n hn a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · apply hseparate a
    exact (sup_le_sup_left (RayClass.localHigherUnitGroup_antitone v hn) _) ha
  · exact Subgroup.mem_sup_left (hpower a ha)

/-- The finite-depth local p-power quotients over S. -/
abbrev localPrimePowerJetProduct (m : RayClass.Modulus k K) (S : Finset (Place k K)) :=
  ∀ v : S, v.val.adicCompletionˣ ⧸
    ((powMonoidHom (α := v.val.adicCompletionˣ) p).range ⊔
      RayClass.localHigherUnitGroup v.val (m v.val))

/-- Localization of actual S-units modulo local powers and higher units. -/
def localPrimePowerJetMap (m : RayClass.Modulus k K) (S : Finset (Place k K)) :
    units k K S →* localPrimePowerJetProduct p m S :=
  MonoidHom.pi fun v =>
    (QuotientGroup.mk' ((powMonoidHom (α := v.val.adicCompletionˣ) p).range ⊔
      RayClass.localHigherUnitGroup v.val (m v.val))).comp
        ((Units.map (algebraMap K v.val.adicCompletion).toMonoidHom).comp
          (units k K S).subtype)

/-- At a supplied finite depth the actual diagonal image has exactly
p^(|S|-1) elements, with kernel the actual S-unit pth powers. -/
theorem exists_localPrimePowerJetMap_ker_card
    (S : Finset (Place k K)) (hS : S.Nonempty) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ m : RayClass.Modulus k K, (∀ v ∈ S, r ≤ m v) →
      (localPrimePowerJetMap p m S).ker =
        (powMonoidHom (α := units k K S) p).range ∧
      Nat.card (MonoidHom.range (G := units k K S)
        (N := localPrimePowerJetProduct p m S) (localPrimePowerJetMap p m S)) =
          p ^ (S.card - 1) := by
  obtain ⟨v, hv⟩ := hS
  obtain ⟨r, hr, hdetect⟩ := exists_primePower_jet_detection p S ⟨v, hv⟩ v
  refine ⟨r, hr, fun m hm => ?_⟩
  have hker : (localPrimePowerJetMap p m S).ker =
      (powMonoidHom (α := units k K S) p).range := by
    apply Subgroup.ext
    intro a
    constructor
    · intro ha
      have hvone := congrFun ha (⟨v, hv⟩ : S)
      exact (hdetect (m v) (hm v hv) a).mp
        ((QuotientGroup.eq_one_iff _).mp hvone)
    · rintro ⟨b, rfl⟩
      apply funext
      intro w
      apply (QuotientGroup.eq_one_iff _).mpr
      apply Subgroup.mem_sup_left
      exact ⟨Units.map (algebraMap K w.val.adicCompletion).toMonoidHom b.val,
        (map_pow (Units.map (algebraMap K w.val.adicCompletion).toMonoidHom)
          b.val p).symm⟩
  refine ⟨hker, ?_⟩
  rw [← Subgroup.index_ker, hker]
  exact card_primePowerQuotient S ⟨v, hv⟩ p

end FunctionField.SUnits
