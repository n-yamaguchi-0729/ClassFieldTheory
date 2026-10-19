/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeleDivisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.IntegralHerbrand

/-!
# The Herbrand quotient of actual S-ideles

For a Galois-stable finite place set, the actual valuation exact sequence has
integral-ideles kernel of Herbrand quotient one and permutation-lattice quotient.
Thus the S-idele quotient is the product of the orbit stabilizer orders.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- Restrict actual extension automorphisms to the stabilizer of a stable finite place set. -/
def galoisStabilizerHom (S : Finset (Place k L))
    (hS : ∀ σ : L ≃ₐ[K] L, ∀ w : Place k L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w ∈ S ↔ w ∈ S) :
    (L ≃ₐ[K] L) →* SUnits.stabilizer k L S :=
  SUnits.stabilizerHom S (SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom k)) hS

/-- The actual finite-extension action on S-ideles. -/
@[reducible]
def sIdeleGaloisAction (S : Finset (Place k L))
    (hS : ∀ σ : L ≃ₐ[K] L, ∀ w : Place k L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w ∈ S ↔ w ∈ S) :
    MulDistribMulAction (L ≃ₐ[K] L) (sIdeles S) :=
  MulDistribMulAction.compHom (sIdeles S) (galoisStabilizerHom S hS)

/-- The actual integral inclusion respects the restricted finite-extension action. -/
theorem integralToSIdeles_equivariant (S : Finset (Place k L))
    (hS : ∀ σ : L ≃ₐ[K] L, ∀ w : Place k L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w ∈ S ↔ w ∈ S) :
    let _ : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles S) := sIdeleGaloisAction S hS
    ∀ (σ : L ≃ₐ[K] L) (a : integralSubgroup (k := k) (K := L)),
      integralToSIdeles S (σ • a) = σ • integralToSIdeles S a := by
  intro hAction σ a
  rfl

/-- The actual valuation sequence is equivariant for the finite-place permutation action. -/
theorem sIdeleDivisor_equivariant (S : Finset (Place k L))
    (hS : ∀ σ : L ≃ₐ[K] L, ∀ w : Place k L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w ∈ S ↔ w ∈ S) :
    let _ : MulAction (L ≃ₐ[K] L) S := MulAction.compHom S (galoisStabilizerHom S hS)
    let _ : MulDistribMulAction (L ≃ₐ[K] L) (S → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    let _ : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles S) := sIdeleGaloisAction S hS
    ∀ (σ : L ≃ₐ[K] L) (a : sIdeles S), sIdeleDivisor S (σ • a) = σ • sIdeleDivisor S a := by
  intro hPlace hCoordinates hIdeles σ a
  funext v
  change sIdeleDivisor S (galoisStabilizerHom S hS σ • a) v =
    sIdeleDivisor S a (galoisStabilizerHom S hS (σ⁻¹) • v)
  rw [map_inv]
  exact sIdeleDivisor_smul S (galoisStabilizerHom S hS σ) a v

end FunctionField.IdeleGroup

namespace FunctionField.IdeleGroup

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [IsCyclic (L ≃ₐ[K] L)]

/-- The actual S-idele Herbrand quotient is the product of its orbit stabilizer orders. -/
theorem sIdeles_herbrandQuotient (S : Finset (Place k L))
    (hS : ∀ σ : L ≃ₐ[K] L, ∀ w : Place k L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w ∈ S ↔ w ∈ S)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    let _ : MulAction (L ≃ₐ[K] L) S := MulAction.compHom S (galoisStabilizerHom S hS)
    let _ : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles S) := sIdeleGaloisAction S hS
    let _ : Fintype (MulAction.orbitRel.Quotient (L ≃ₐ[K] L) S) := Fintype.ofFinite _
    ∃ hJ : HerbrandQuotientDefined (L ≃ₐ[K] L) (sIdeles S) σ,
      let _ : Finite (HerbrandH0 (L ≃ₐ[K] L) (sIdeles S)) := hJ.1
      let _ : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (sIdeles S) σ) := hJ.2
      herbrandQuotient (G := L ≃ₐ[K] L) (A := sIdeles S) σ =
        ∏ ω : MulAction.orbitRel.Quotient (L ≃ₐ[K] L) S,
          (Nat.card (permutationOrbitStabilizer ω) : ℚ) := by
  intro hPlace hAction hOrbits
  let : MulDistribMulAction (L ≃ₐ[K] L) (S → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  obtain ⟨hU, hUvalue⟩ := integralIdeles_herbrandQuotient (k := k) σ hgen
  have hP : HerbrandQuotientDefined (L ≃ₐ[K] L) (S → Multiplicative ℤ) σ :=
    ⟨permutationFunctionHerbrandH0Finite σ hgen,
      permutationFunctionHerbrandHMinusOneFinite σ hgen⟩
  have hJ := herbrandQuotientDefined_middle_of_left_right
    (integralToSIdeles S) (sIdeleDivisor S)
    (integralToSIdeles_equivariant S hS) (sIdeleDivisor_equivariant S hS)
    (sIdeleDivisor_exact S) (integralToSIdeles_injective S) (sIdeleDivisor_surjective S)
    σ hgen hU hP
  refine ⟨hJ, ?_⟩
  intro hJ0 hJm
  have : Finite (HerbrandH0 (L ≃ₐ[K] L) (integralSubgroup (k := k) (K := L))) := hU.1
  have : Finite (HerbrandHMinusOne (L ≃ₐ[K] L)
      (integralSubgroup (k := k) (K := L)) σ) := hU.2
  have : Finite (HerbrandH0 (L ≃ₐ[K] L) (S → Multiplicative ℤ)) := hP.1
  have : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (S → Multiplicative ℤ) σ) := hP.2
  have h := herbrandQuotient_multiplicative_of_shortExact
    (integralToSIdeles S) (sIdeleDivisor S)
    (integralToSIdeles_equivariant S hS) (sIdeleDivisor_equivariant S hS)
    (sIdeleDivisor_exact S) (integralToSIdeles_injective S) (sIdeleDivisor_surjective S) σ hgen
  rw [hUvalue, one_mul] at h
  let : ∀ ω : MulAction.orbitRel.Quotient (L ≃ₐ[K] L) S,
      Fintype (permutationOrbitStabilizer ω) := fun _ => Fintype.ofFinite _
  rw [permutationFunction_herbrandQuotient_eq_stabilizerProduct σ hgen] at h
  simpa only [Nat.card_eq_fintype_card] using h

end FunctionField.IdeleGroup
