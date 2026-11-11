/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.HasseNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.ClassHerbrand
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.IntegralTateComparison
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# The cyclic class-field axiom for actual function-field idele classes

The Hasse norm theorem kills the actual class norm obstruction. Together with
the proved Herbrand quotient this computes the norm index and both low-degree
Tate groups, without requiring an intermediate-field presentation.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField.IdeleClassGroup

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

section Arithmetic

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual class norm obstruction vanishes for every finite cyclic extension. -/
theorem herbrandHMinusOne_subsingleton
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) :
    Subsingleton (HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g) := by
  have hcyc : IsCyclic Gal(L/K) := ⟨⟨g, hg⟩⟩
  have hplace : Nonempty (Place k K) := FunctionField.nonempty_place k K
  apply (NormObstruction.hasseNormDiagonal_injective_iff_class_herbrandHMinusOne_subsingleton
    (k := k) g hg).mp
  exact NormObstruction.hasseNormDiagonal_injective_iff.mpr
    (NormObstruction.principalNormSubgroup_eq_fieldNormSubgroup
      (k := k) (K := K) (L := L)).le

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- The norm index of the actual idele class group equals the cyclic extension degree. -/
theorem card_normQuotient_eq_finrank
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) :
    Nat.card (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) =
      Module.finrank K L := by
  obtain ⟨hC, hvalue⟩ := herbrandQuotient_eq_card (k := k) g hg
  have hfinite : Finite (HerbrandH0 Gal(L/K) (IdeleClassGroup k L)) := hC.1
  have hminus : Subsingleton (HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g) :=
    herbrandHMinusOne_subsingleton (k := k) g hg
  rw [Nat.card_congr (normQuotientEquivHerbrandH0 (k := k) (K := K) (L := L)).toEquiv,
    herbrandH0_card_eq_mul_herbrandHMinusOne_card g (Nat.card Gal(L/K)) hvalue,
    Nat.card_unique (α := HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g), mul_one]
  exact IsGalois.card_aut_eq_finrank K L

/-- The actual integral Tate groups have the arithmetic class-field cardinalities
for independent original constant, base-field and upper-field universes. -/
theorem integral_tate_lowDegree_finite_card_eq_finrank
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) :
    let A := Rep.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup k L)
    Finite (IntegralGroupCohomology.Universe.tate A 0) ∧
      Finite (IntegralGroupCohomology.Universe.tate A (-1)) ∧
      Nat.card (IntegralGroupCohomology.Universe.tate A 0) = Module.finrank K L ∧
      Nat.card (IntegralGroupCohomology.Universe.tate A (-1)) = 1 := by
  intro A
  obtain ⟨hC, _⟩ := herbrandQuotient_eq_card (k := k) g hg
  have hfinite : Finite (HerbrandH0 Gal(L/K) (IdeleClassGroup k L)) := hC.1
  have hminus : Subsingleton (HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g) :=
    herbrandHMinusOne_subsingleton (k := k) g hg
  let e0 := (integralTateH0EquivHerbrandH0 (G := Gal(L/K))
    (A := IdeleClassGroup k L) g hg).toEquiv
  let em := (integralTateHMinusOneEquivHerbrandHMinusOne (G := Gal(L/K))
    (A := IdeleClassGroup k L) g hg).toEquiv
  have h0finite : Finite (IntegralGroupCohomology.Universe.tate A 0) :=
    Finite.of_injective e0 e0.injective
  have hmfinite : Finite (IntegralGroupCohomology.Universe.tate A (-1)) :=
    Finite.of_injective em em.injective
  refine ⟨h0finite, hmfinite, ?_, ?_⟩
  · rw [Nat.card_congr e0]
    change Nat.card (HerbrandH0 Gal(L/K) (IdeleClassGroup k L)) = Module.finrank K L
    rw [← Nat.card_congr (normQuotientEquivHerbrandH0 (k := k) (K := K) (L := L)).toEquiv]
    exact card_normQuotient_eq_finrank g hg
  · rw [Nat.card_congr em]
    exact Nat.card_unique

end Arithmetic

section NativeCohomology

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- Finiteness and exact cardinalities in the actual Tate-cohomology formulation
of the cyclic class-field axiom. -/
theorem tate_lowDegree_finite_card_eq_finrank
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) :
    let A := Rep.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup k L)
    Finite (tateCohomology A 0) ∧ Finite (tateCohomology A (-1)) ∧
      Nat.card (tateCohomology A 0) = Module.finrank K L ∧
      Nat.card (tateCohomology A (-1)) = 1 := by
  intro A
  obtain ⟨hC, _⟩ := herbrandQuotient_eq_card (k := k) g hg
  have hfinite : Finite (HerbrandH0 Gal(L/K) (IdeleClassGroup k L)) := hC.1
  have hminus : Subsingleton (HerbrandHMinusOne Gal(L/K) (IdeleClassGroup k L) g) :=
    herbrandHMinusOne_subsingleton (k := k) g hg
  let e0 := (tateH0IsoHerbrandH0 (G := Gal(L/K))
    (A := IdeleClassGroup k L)).toLinearEquiv.toEquiv
  let em := (tateHMinusOneIsoHerbrandHMinusOne (G := Gal(L/K))
    (A := IdeleClassGroup k L) g hg).toLinearEquiv.toEquiv
  have h0finite : Finite (tateCohomology A 0) := Finite.of_injective e0 e0.injective
  have hmfinite : Finite (tateCohomology A (-1)) := Finite.of_injective em em.injective
  refine ⟨h0finite, hmfinite, ?_, ?_⟩
  · rw [Nat.card_congr e0]
    change Nat.card (HerbrandH0 Gal(L/K) (IdeleClassGroup k L)) = Module.finrank K L
    rw [← Nat.card_congr (normQuotientEquivHerbrandH0 (k := k) (K := K) (L := L)).toEquiv]
    exact card_normQuotient_eq_finrank g hg
  · rw [Nat.card_congr em]
    exact Nat.card_unique

end NativeCohomology

end FunctionField.IdeleClassGroup
