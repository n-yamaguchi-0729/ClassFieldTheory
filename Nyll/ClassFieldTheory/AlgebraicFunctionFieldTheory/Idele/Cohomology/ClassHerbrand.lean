/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeleHerbrand
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedNormQuotient
import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Index

/-!
# The actual idele-class Herbrand quotient and first norm inequality

A stable finite S-idele presentation is supplied by the actual Picard group.
The S-unit and S-idele computations cancel their common orbit factor, giving
`h(G, C_L) = |G|`. The actual norm quotient consequently has order at least
`[L : K]`. No Hasse norm principle or upper norm-index bound is assumed.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve CyclicCohomology

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [HasPrincipalDivisors k L]

/-- The diagonal S-unit map respects the actual finite-extension action. -/
theorem sUnitDiagonal_equivariant (S : Finset (Place k L))
    (hS : ∀ σ : L ≃ₐ[K] L, ∀ w : Place k L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w ∈ S ↔ w ∈ S) :
    let _ : MulDistribMulAction (L ≃ₐ[K] L) (SUnits.units k L S) :=
      SUnits.unitsAction S (galoisStabilizerHom S hS)
    let _ : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles S) := sIdeleGaloisAction S hS
    ∀ (σ : L ≃ₐ[K] L) (u : SUnits.units k L S),
      sUnitDiagonal S (σ • u) = σ • sUnitDiagonal S u := by
  intro hUnits hIdeles σ u
  exact sUnitDiagonal_smul S (galoisStabilizerHom S hS σ) u

/-- The S-idele class map respects the actual finite-extension action. -/
theorem sIdeleClass_equivariant (S : Finset (Place k L))
    (hS : ∀ σ : L ≃ₐ[K] L, ∀ w : Place k L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w ∈ S ↔ w ∈ S) :
    let _ : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles S) := sIdeleGaloisAction S hS
    ∀ (σ : L ≃ₐ[K] L) (a : sIdeles S), sIdeleClass S (σ • a) = σ • sIdeleClass S a := by
  intro hIdeles σ a
  exact sIdeleClass_smul S (galoisStabilizerHom S hS σ) a

end FunctionField.IdeleGroup

namespace FunctionField.IdeleClassGroup

open AlgebraicCurve CyclicCohomology IdeleGroup
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- The actual idele-class Herbrand quotient of a finite cyclic extension is its degree. -/
theorem herbrandQuotient_eq_card (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ∃ hC : HerbrandQuotientDefined (L ≃ₐ[K] L) (IdeleClassGroup k L) σ,
      let _ : Finite (HerbrandH0 (L ≃ₐ[K] L) (IdeleClassGroup k L)) := hC.1
      let _ : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (IdeleClassGroup k L) σ) := hC.2
      herbrandQuotient (G := L ≃ₐ[K] L) (A := IdeleClassGroup k L) σ =
        (Nat.card (L ≃ₐ[K] L) : ℚ) := by
  classical
  -- Share the canonical quotient structure when elaborating the two exact-sequence maps.
  let : CommGroup (IdeleClassGroup k L) := inferInstance
  let hClassAction : MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup k L) :=
    galoisMulDistribMulAction (k := k) (K := K) (L := L)
  let : SMul (L ≃ₐ[K] L) (IdeleClassGroup k L) := hClassAction.toMulAction.toSMul
  let : MulAction (L ≃ₐ[K] L) (IdeleClassGroup k L) := hClassAction.toMulAction
  have : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, hgen⟩⟩
  obtain ⟨w⟩ := FunctionField.nonempty_place k L
  let ρ : (L ≃ₐ[K] L) →* SemilinearAut k L :=
    SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom k)
  obtain ⟨S, hwS, hS, hsurj⟩ := exists_finset_stable_sIdeleClass_surjective k L ρ {w}
  have hSne : S.Nonempty := ⟨w, hwS (Finset.mem_singleton_self w)⟩
  let r := galoisStabilizerHom S hS
  let : MulAction (L ≃ₐ[K] L) S := MulAction.compHom S r
  let : MulDistribMulAction (L ≃ₐ[K] L) (SUnits.units k L S) := SUnits.unitsAction S r
  let : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles (k := k) (K := L) S) := sIdeleGaloisAction S hS
  let : Fintype (MulAction.orbitRel.Quotient (L ≃ₐ[K] L) S) := Fintype.ofFinite _
  obtain ⟨hU, hUvalue⟩ := SUnits.units_herbrandQuotient S hSne r σ hgen
  obtain ⟨hJ, hJvalue⟩ := sIdeles_herbrandQuotient S hS σ hgen
  have hexact : ∀ a : sIdeles (k := k) (K := L) S,
      sIdeleClass (k := k) (K := L) S a = 1 ↔
        ∃ u, sUnitDiagonal (k := k) (K := L) S u = a := by
    intro a
    change a ∈ (sIdeleClass (k := k) (K := L) S).ker ↔ a ∈ (sUnitDiagonal (k := k) (K := L) S).range
    rw [range_sUnitDiagonal]
  let i : SUnits.units k L S →* sIdeles (k := k) (K := L) S :=
    sUnitDiagonal (k := k) (K := L) S
  let j : sIdeles (k := k) (K := L) S →* IdeleClassGroup k L :=
    sIdeleClass (k := k) (K := L) S
  have hi : ∀ (τ : L ≃ₐ[K] L) (u : SUnits.units k L S), i (τ • u) = τ • i u :=
    sUnitDiagonal_equivariant S hS
  have hj : ∀ (τ : L ≃ₐ[K] L) (a : sIdeles (k := k) (K := L) S),
      j (τ • a) = τ • j a := sIdeleClass_equivariant S hS
  have hsurj' : Function.Surjective j := hsurj
  have hC := herbrandQuotientDefined_right_of_left_middle
    (G := L ≃ₐ[K] L) (A := SUnits.units k L S)
    (B := sIdeles (k := k) (K := L) S) (C := IdeleClassGroup k L)
    i j hi hj hexact (sUnitDiagonal_injective S) hsurj' σ hgen hU hJ
  refine ⟨hC, ?_⟩
  intro hC0 hCm
  have : Finite (HerbrandH0 (L ≃ₐ[K] L) (SUnits.units k L S)) := hU.1
  have : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (SUnits.units k L S) σ) := hU.2
  have : Finite (HerbrandH0 (L ≃ₐ[K] L) (sIdeles (k := k) (K := L) S)) := hJ.1
  have : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (sIdeles (k := k) (K := L) S) σ) := hJ.2
  have h := herbrandQuotient_multiplicative_of_shortExact
    (G := L ≃ₐ[K] L) (A := SUnits.units k L S)
    (B := sIdeles (k := k) (K := L) S) (C := IdeleClassGroup k L)
    i j hi hj hexact (sUnitDiagonal_injective S) hsurj' σ hgen
  rw [hUvalue, hJvalue] at h
  have hq : (∏ ω : MulAction.orbitRel.Quotient (L ≃ₐ[K] L) S,
      (Nat.card (permutationOrbitStabilizer ω) : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ω _
    exact Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  have hn : (Nat.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  apply (mul_left_cancel₀ (div_ne_zero hq hn))
  rw [div_mul_cancel₀ _ hn]
  exact h.symm

/-- First norm inequality for the actual idele-class norm quotient in a finite cyclic extension. -/
theorem finrank_le_card_normQuotient (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    Module.finrank K L ≤ Nat.card
      (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) := by
  obtain ⟨hC, hvalue⟩ := herbrandQuotient_eq_card (k := k) σ hgen
  have : Finite (HerbrandH0 (L ≃ₐ[K] L) (IdeleClassGroup k L)) := hC.1
  have : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (IdeleClassGroup k L) σ) := hC.2
  rw [Nat.card_congr (normQuotientEquivHerbrandH0 (k := k) (K := K) (L := L)).toEquiv]
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
    exact IsGalois.card_aut_eq_finrank K L
  rw [← hcard]
  exact le_herbrandH0_card_of_herbrandQuotient_eq_nat σ (Nat.card (L ≃ₐ[K] L)) hvalue

end FunctionField.IdeleClassGroup
