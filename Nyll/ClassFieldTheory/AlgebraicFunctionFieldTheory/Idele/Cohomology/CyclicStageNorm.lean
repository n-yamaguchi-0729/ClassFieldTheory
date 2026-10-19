/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.CyclicUnitsH2
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.ClassHerbrand

/-!
# Hasse norms and the class-field index at cyclic stages

The proved local-global principle for unit H² gives the Hasse norm theorem
for every finite cyclic stage. The concrete norm obstruction and Herbrand
quotient then give Tate H⁻¹ vanishing and the exact idele-class norm index.
-/

noncomputable section

open AlgebraicCurve

namespace FunctionField

open ClassFieldTower.Cohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- The Hasse norm theorem for an actual finite cyclic intermediate field. -/
theorem principalNormSubgroup_eq_fieldNormSubgroup_cyclicStage
    (L : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(L/K)] :
    NormObstruction.principalNormSubgroup (k := k) (K := K) (L := L) =
      NormObstruction.fieldNormSubgroup (K := K) (L := L) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
    have hlocal := (IdeleGroup.baseUnitH2Class_locally_zero_iff_principal_norm
      (k := k) g hg a).mpr ha
    have hzero := cyclicUnitsH2_eq_zero_of_forall_completion k K Ω L
      (finiteCyclicBaseUnitH2Class K L g hg a) hlocal
    obtain ⟨x, hx⟩ := (finiteCyclicBaseUnitH2Class_eq_zero_iff_norm K L g hg a).mp hzero
    have hxne : x ≠ 0 := by
      intro h
      rw [h, Algebra.norm_zero] at hx
      exact a.ne_zero hx.symm
    exact ⟨Units.mk0 x hxne, Units.ext hx⟩
  · exact NormObstruction.fieldNormSubgroup_le_principalNormSubgroup

open CyclicCohomology CyclicCohomology.ProfiniteCohomology.Herbrand

/-- The actual idele class group has trivial cyclic Tate H⁻¹ at every finite stage. -/
theorem classHerbrandHMinusOne_subsingleton_cyclicStage
    (L : FiniteGaloisIntermediateField K Ω)
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) :
    Subsingleton (HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g) := by
  have hcyc : IsCyclic Gal(L/K) := ⟨⟨g, hg⟩⟩
  have hplace : Nonempty (Place k K) := FunctionField.nonempty_place k K
  apply (NormObstruction.hasseNormDiagonal_injective_iff_class_herbrandHMinusOne_subsingleton
    (k := k) g hg).mp
  exact NormObstruction.hasseNormDiagonal_injective_iff.mpr
    (principalNormSubgroup_eq_fieldNormSubgroup_cyclicStage k K Ω L).le

/-- The actual idele-class norm quotient has exactly the cyclic extension degree. -/
theorem card_normQuotient_cyclicStage
    (L : FiniteGaloisIntermediateField K Ω)
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) :
    Nat.card (IdeleClassGroup k K ⧸
      (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) = Module.finrank K L := by
  obtain ⟨hC, hvalue⟩ := IdeleClassGroup.herbrandQuotient_eq_card (k := k) g hg
  have hfinite : Finite (HerbrandH0 Gal(L/K) (IdeleClassGroup k L)) := hC.1
  have hminus : Subsingleton (HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g) :=
    classHerbrandHMinusOne_subsingleton_cyclicStage k K Ω L g hg
  rw [Nat.card_congr (IdeleClassGroup.normQuotientEquivHerbrandH0
    (k := k) (K := K) (L := L)).toEquiv]
  rw [herbrandH0_card_eq_mul_herbrandHMinusOne_card g (Nat.card Gal(L/K)) hvalue,
    Nat.card_unique (α := HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g), mul_one]
  exact IsGalois.card_aut_eq_finrank K L

end FunctionField
