/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitLocalPowerIndex
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeles
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SupportedComponents
import Mathlib.GroupTheory.Index

/-!
# Actual idele classes with power components on S

The local power projection of S-ideles is surjective. Its kernel maps to
an actual idele-class subgroup. The two surjections, to idele classes and
to local power classes, identify its index with the already computed
index of diagonal S-units in the local product.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- The local power classes of an actual S-idele. -/
def sIdelePowerClass (n : ℕ+) (S : Finset (Place k K)) :
    sIdeles S →* SUnits.localPowerClassProduct n S :=
  MonoidHom.pi fun v =>
    (QuotientGroup.mk' (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range).comp
      ((component v.val).comp (sIdeles S).subtype)

/-- Every tuple of local power classes has an S-supported idele representative. -/
theorem sIdelePowerClass_surjective (n : ℕ+) (S : Finset (Place k K)) :
    Function.Surjective (sIdelePowerClass (k := k) (K := K) n S) := by
  classical
  intro c
  choose x hx using fun v : S => QuotientGroup.mk'_surjective
    (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range (c v)
  obtain ⟨a, hain, _⟩ := exists_supported_sIdele S x
  refine ⟨a, ?_⟩
  apply funext
  intro v
  change QuotientGroup.mk' (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range
    (a.val v.val) = c v
  rw [hain v]
  exact hx v

variable [HasPrincipalDivisors k K]

/-- The actual idele-class subgroup represented by S-ideles whose components
at S are powers. Outside S the representative is integral and invertible. -/
def powerClassSubgroup (n : ℕ+) (S : Finset (Place k K)) :
    Subgroup (IdeleClassGroup k K) :=
  (sIdelePowerClass (k := k) (K := K) n S).ker.map (sIdeleClass S)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The subgroup of actual power-component classes has the Kummer degree as index. -/
theorem index_powerClassSubgroup (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (S : Finset (Place k K))
    (hSne : S.Nonempty) (hS : Function.Surjective (sIdeleClass S)) :
    (powerClassSubgroup n S).index = (n : ℕ) ^ S.card := by
  let f : sIdeles S →* IdeleClassGroup k K := sIdeleClass S
  let g : sIdeles S →* SUnits.localPowerClassProduct n S := sIdelePowerClass n S
  have hg : Function.Surjective g := sIdelePowerClass_surjective n S
  have hdiag : f.ker.map g =
      MonoidHom.range (G := SUnits.units k K S) (N := SUnits.localPowerClassProduct n S)
        (SUnits.localPowerClassMap n S) := by
    ext c
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := (range_sUnitDiagonal S).ge ha
      refine ⟨b, ?_⟩
      rw [← hb]
      rfl
    · rintro ⟨b, rfl⟩
      exact ⟨sUnitDiagonal S b, (range_sUnitDiagonal S).le ⟨b, rfl⟩, rfl⟩
  have hleft : (powerClassSubgroup n S).index = (g.ker ⊔ f.ker).index := by
    change (g.ker.map f).index = _
    rw [Subgroup.index_map, f.range_eq_top_of_surjective hS, Subgroup.index_top, mul_one]
  have hright : (Subgroup.map (N := SUnits.localPowerClassProduct n S) g f.ker).index =
      (f.ker ⊔ g.ker).index := by
    rw [Subgroup.index_map, MonoidHom.range_eq_top_of_surjective (G := sIdeles S)
      (N := SUnits.localPowerClassProduct n S) g hg, Subgroup.index_top, mul_one]
  rw [hleft, sup_comm, ← hright, hdiag]
  exact SUnits.index_localPowerClassMap_range n hn hmu S hSne hS

end FunctionField.IdeleGroup
