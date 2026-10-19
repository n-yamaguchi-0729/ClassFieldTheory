/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitPrimePowerJets
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitPowerRay
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SupportedComponents

/-!
# Finite-depth power classes of actual S-ideles

The two surjections from S-ideles identify the index of the class subgroup
with the index of the actual diagonal S-unit image in the local jet product.
Local power-and-unit representatives factor into an actual global power
and a ray-congruent idele.
-/

noncomputable section
open AlgebraicCurve
namespace FunctionField.IdeleGroup

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- The local p-power jets of an actual S-idele. -/
def sIdelePrimePowerJet (p : ℕ) (m : RayClass.Modulus k K) (S : Finset (Place k K)) :
    sIdeles S →* SUnits.localPrimePowerJetProduct p m S :=
  MonoidHom.pi fun v =>
    (QuotientGroup.mk' ((powMonoidHom (α := v.val.adicCompletionˣ) p).range ⊔
      RayClass.localHigherUnitGroup v.val (m v.val))).comp
        ((component v.val).comp (sIdeles S).subtype)

/-- Finite local jet data has an actual S-supported idele representative. -/
theorem sIdelePrimePowerJet_surjective (p : ℕ) (m : RayClass.Modulus k K)
    (S : Finset (Place k K)) :
    Function.Surjective (sIdelePrimePowerJet (k := k) (K := K) p m S) := by
  classical
  intro c
  choose x hx using fun v : S => QuotientGroup.mk'_surjective
    ((powMonoidHom (α := v.val.adicCompletionˣ) p).range ⊔
      RayClass.localHigherUnitGroup v.val (m v.val)) (c v)
  obtain ⟨a, hain, _⟩ := exists_supported_sIdele S x
  refine ⟨a, ?_⟩
  apply funext
  intro v
  change QuotientGroup.mk' ((powMonoidHom (α := v.val.adicCompletionˣ) p).range ⊔
    RayClass.localHigherUnitGroup v.val (m v.val)) (a.val v.val) = c v
  rw [hain v]
  exact hx v

variable [HasPrincipalDivisors k K]

/-- The actual classes with power-and-higher-unit components on S. -/
def primePowerJetClassSubgroup (p : ℕ) (m : RayClass.Modulus k K)
    (S : Finset (Place k K)) : Subgroup (IdeleClassGroup k K) :=
  (sIdelePrimePowerJet (k := k) (K := K) p m S).ker.map (sIdeleClass S)

/-- The actual diagonal S-unit image computes the class subgroup's index. -/
theorem index_primePowerJetClassSubgroup (p : ℕ) (m : RayClass.Modulus k K)
    (S : Finset (Place k K)) (hS : Function.Surjective (sIdeleClass S)) :
    (primePowerJetClassSubgroup p m S).index =
      (MonoidHom.range (G := SUnits.units k K S)
        (N := SUnits.localPrimePowerJetProduct p m S)
        (SUnits.localPrimePowerJetMap p m S)).index := by
  let f : sIdeles S →* IdeleClassGroup k K := sIdeleClass S
  let g : sIdeles S →* SUnits.localPrimePowerJetProduct p m S := sIdelePrimePowerJet p m S
  have hg : Function.Surjective g := sIdelePrimePowerJet_surjective p m S
  have hdiag : f.ker.map g =
      MonoidHom.range (G := SUnits.units k K S) (N := SUnits.localPrimePowerJetProduct p m S)
        (SUnits.localPrimePowerJetMap p m S) := by
    ext c
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := (range_sUnitDiagonal S).ge ha
      refine ⟨b, ?_⟩
      rw [← hb]
      rfl
    · rintro ⟨b, rfl⟩
      exact ⟨sUnitDiagonal S b, (range_sUnitDiagonal S).le ⟨b, rfl⟩, rfl⟩
  have hleft : (primePowerJetClassSubgroup p m S).index = (g.ker ⊔ f.ker).index := by
    change (g.ker.map f).index = _
    rw [Subgroup.index_map, f.range_eq_top_of_surjective hS, Subgroup.index_top, mul_one]
  have hright : (Subgroup.map (N := SUnits.localPrimePowerJetProduct p m S) g f.ker).index =
      (f.ker ⊔ g.ker).index := by
    rw [Subgroup.index_map, MonoidHom.range_eq_top_of_surjective (G := sIdeles S)
      (N := SUnits.localPrimePowerJetProduct p m S) g hg, Subgroup.index_top, mul_one]
  rw [hleft, sup_comm, ← hright, hdiag]

/-- Local jet congruences produce actual ray-power classes. -/
theorem primePowerJetClassSubgroup_le_powerRaySubgroup (p : ℕ)
    (m : RayClass.Modulus k K) (S : Finset (Place k K)) (hm : m.support ⊆ S) :
    primePowerJetClassSubgroup p m S ≤ RayClass.powerRaySubgroup m p := by
  rintro c ⟨a, ha, rfl⟩
  apply sIdeleClass_mem_powerRaySubgroup_of_local p S m hm a
  intro v
  exact (QuotientGroup.eq_one_iff _).mp (congrFun ha v)

end FunctionField.IdeleGroup
