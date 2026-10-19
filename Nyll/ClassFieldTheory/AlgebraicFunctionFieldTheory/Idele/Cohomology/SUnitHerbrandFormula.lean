/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitHerbrand

/-!
# The numerical Herbrand quotient of S-units

The actual weighted-degree sequence identifies the quotient of the finite permutation
lattice by the degree-zero lattice with a trivial infinite cyclic group. This computes
the Herbrand quotient using orbit stabilizers, without assuming a degree-one place.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The actual divisor lattice embedded in its multiplicative place coordinates. -/
def latticeCoordinates (S : Finset (Place k K)) :
    Multiplicative (divisorLattice k K S) →* (S → Multiplicative ℤ) where
  toFun D v := Multiplicative.ofAdd (coordinates S D.toAdd v)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem latticeCoordinates_injective (S : Finset (Place k K)) :
    Function.Injective (latticeCoordinates S) := by
  intro D E h
  apply Multiplicative.ext
  apply coordinates_injective S
  exact funext fun v => congrArg Multiplicative.toAdd (congrFun h v)

variable [IsCurveOver k K]

/-- Weighted degree, expressed in a generator of its actual nonzero image. -/
def coordinateDegree (S : Finset (Place k K)) (hS : S.Nonempty) :
    (S → Multiplicative ℤ) →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd
    (degreeRangeEquivInt S hS ((weightedDegree S).rangeRestrict fun v => (a v).toAdd))
  map_one' := by
    apply Multiplicative.ext
    change degreeRangeEquivInt S hS ((weightedDegree S).rangeRestrict 0) = 0
    rw [map_zero, map_zero]
  map_mul' a b := by
    apply Multiplicative.ext
    change degreeRangeEquivInt S hS ((weightedDegree S).rangeRestrict
      ((fun v => (a v).toAdd) + (fun v => (b v).toAdd))) = _
    rw [map_add, map_add]
    rfl

theorem coordinateDegree_surjective (S : Finset (Place k K)) (hS : S.Nonempty) :
    Function.Surjective (coordinateDegree S hS) := by
  intro n
  obtain ⟨a, ha⟩ := (weightedDegree S).rangeRestrict_surjective
    ((degreeRangeEquivInt S hS).symm n.toAdd)
  refine ⟨fun v => Multiplicative.ofAdd (a v), ?_⟩
  apply Multiplicative.ext
  change degreeRangeEquivInt S hS ((weightedDegree S).rangeRestrict a) = n.toAdd
  rw [ha, AddEquiv.apply_symm_apply]

theorem coordinateDegree_exact (S : Finset (Place k K)) (hS : S.Nonempty)
    (a : S → Multiplicative ℤ) :
    coordinateDegree S hS a = 1 ↔ ∃ D, latticeCoordinates S D = a := by
  constructor
  · intro ha
    have hz : weightedDegree S (fun v => (a v).toAdd) = 0 := by
      have h := (degreeRangeEquivInt S hS).injective
        ((congrArg Multiplicative.toAdd ha).trans (map_zero _).symm)
      exact congrArg Subtype.val h
    let D := (latticeEquivDegreeKernel S).symm ⟨fun v => (a v).toAdd, hz⟩
    refine ⟨Multiplicative.ofAdd D, ?_⟩
    funext v
    apply Multiplicative.ext
    exact congrFun (congrArg Subtype.val
      ((latticeEquivDegreeKernel S).apply_symm_apply ⟨fun v => (a v).toAdd, hz⟩)) v
  · rintro ⟨D, rfl⟩
    apply Multiplicative.ext
    change degreeRangeEquivInt S hS
      ((weightedDegree S).rangeRestrict (coordinates S D.toAdd)) = 0
    have hz : (weightedDegree S).rangeRestrict (coordinates S D.toAdd) = 0 :=
      Subtype.ext (latticeEquivDegreeKernel S D.toAdd).2
    rw [hz, map_zero]

variable {G : Type*} [Group G]

omit [IsCurveOver k K] in
/-- The coordinate embedding intertwines the actual divisor action and place permutation. -/
theorem latticeCoordinates_equivariant (S : Finset (Place k K))
    (ρ : G →* stabilizer k K S) :
    let _ : MulAction G S := MulAction.compHom S ρ
    let _ : MulDistribMulAction G (S → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    let _ : MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := latticeAction S ρ
    ∀ (g : G) (D : Multiplicative (divisorLattice k K S)),
      latticeCoordinates S (g • D) = g • latticeCoordinates S D := by
  intro hPlace hCoordinates hLattice g D
  funext v
  apply Multiplicative.ext
  change coordinates S (ρ g • D.toAdd) v = coordinates S D.toAdd (ρ (g⁻¹) • v)
  rw [map_inv]
  exact congrFun (coordinates_smul S (ρ g) D.toAdd) v

/-- Normalized coordinate degree has trivial Galois action. -/
theorem coordinateDegree_equivariant (S : Finset (Place k K)) (hS : S.Nonempty)
    (ρ : G →* stabilizer k K S) :
    let _ : MulAction G S := MulAction.compHom S ρ
    let _ : MulDistribMulAction G (S → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    let _ : MulDistribMulAction G (Multiplicative ℤ) := trivialIntMulDistribMulAction G
    let _ : SMul G (S → Multiplicative ℤ) :=
      (permutationFunctionMulDistribMulAction (G := G) (ι := S)).toMulAction.toSMul
    ∀ (g : G) (a : S → Multiplicative ℤ),
      coordinateDegree S hS (g • a) = g • coordinateDegree S hS a := by
  intro hPlace hCoordinates hInt hCoordinateSMul g a
  apply congrArg Multiplicative.ofAdd
  apply congrArg (degreeRangeEquivInt S hS)
  apply Subtype.ext
  change weightedDegree S (fun v => (a (ρ (g⁻¹) • v)).toAdd) =
    weightedDegree S (fun v => (a v).toAdd)
  rw [map_inv]
  exact weightedDegree_smul S (ρ g) (fun v => (a v).toAdd)

end FunctionField.SUnits

namespace FunctionField.SUnits

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K G : Type} [Field k] [Field K] [Algebra k K]
    [IsCurveOver k K] [Group G] [Fintype G]

/-- The degree-zero divisor lattice has the permutation stabilizer product divided by `|G|`. -/
theorem lattice_herbrandQuotient (S : Finset (Place k K)) (hS : S.Nonempty)
    (ρ : G →* stabilizer k K S) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    let _ : MulAction G S := MulAction.compHom S ρ
    let _ : MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := latticeAction S ρ
    let _ : Fintype (MulAction.orbitRel.Quotient G S) := Fintype.ofFinite _
    ∃ hL : HerbrandQuotientDefined G (Multiplicative (divisorLattice k K S)) σ,
      let _ : Finite (HerbrandH0 G (Multiplicative (divisorLattice k K S))) := hL.1
      let _ : Finite (HerbrandHMinusOne G (Multiplicative (divisorLattice k K S)) σ) := hL.2
      herbrandQuotient (G := G) (A := Multiplicative (divisorLattice k K S)) σ =
        (∏ ω : MulAction.orbitRel.Quotient G S,
          (Nat.card (permutationOrbitStabilizer ω) : ℚ)) / (Nat.card G : ℚ) := by
  intro hPlace hLattice hOrbits
  let hCoordinates : MulDistribMulAction G (S → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let : MulDistribMulAction G (Multiplicative ℤ) := trivialIntMulDistribMulAction G
  -- A direct scalar instance prevents the pointwise action on functions from replacing
  -- the permutation action when the trivial action on the integer target is installed.
  let : SMul G (S → Multiplicative ℤ) := hCoordinates.toMulAction.toSMul
  have hB : HerbrandQuotientDefined G (S → Multiplicative ℤ) σ :=
    ⟨permutationFunctionHerbrandH0Finite σ hgen,
      permutationFunctionHerbrandHMinusOneFinite σ hgen⟩
  have hC : HerbrandQuotientDefined G (Multiplicative ℤ) σ :=
    ⟨trivialIntHerbrandH0Finite, trivialIntHerbrandHMinusOneFinite σ⟩
  have hL := herbrandQuotientDefined_left_of_middle_right
    (latticeCoordinates S) (coordinateDegree S hS)
    (latticeCoordinates_equivariant S ρ) (coordinateDegree_equivariant S hS ρ)
    (coordinateDegree_exact S hS) (latticeCoordinates_injective S)
    (coordinateDegree_surjective S hS) σ hgen hB hC
  refine ⟨hL, ?_⟩
  intro hL0 hLm
  have : Finite (HerbrandH0 G (S → Multiplicative ℤ)) := hB.1
  have : Finite (HerbrandHMinusOne G (S → Multiplicative ℤ) σ) := hB.2
  have : Finite (HerbrandH0 G (Multiplicative ℤ)) := hC.1
  have : Finite (HerbrandHMinusOne G (Multiplicative ℤ) σ) := hC.2
  have hmul := herbrandQuotient_multiplicative_of_shortExact
    (latticeCoordinates S) (coordinateDegree S hS)
    (latticeCoordinates_equivariant S ρ) (coordinateDegree_equivariant S hS ρ)
    (coordinateDegree_exact S hS) (latticeCoordinates_injective S)
    (coordinateDegree_surjective S hS) σ hgen
  let : ∀ ω : MulAction.orbitRel.Quotient G S,
      Fintype (permutationOrbitStabilizer ω) := fun _ => Fintype.ofFinite _
  rw [permutationFunction_herbrandQuotient_eq_stabilizerProduct σ hgen,
    trivialInt_herbrandQuotient_eq_card σ] at hmul
  simp only [Nat.card_eq_fintype_card]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card G ≠ 0))).mpr
  exact hmul.symm

omit [IsCurveOver k K] in
/-- The actual S-unit Herbrand quotient is the orbit stabilizer product divided by `|G|`. -/
theorem units_herbrandQuotient [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K] [HasPrincipalDivisors k K]
    (S : Finset (Place k K)) (hS : S.Nonempty)
    (ρ : G →* stabilizer k K S) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    let _ : MulAction G S := MulAction.compHom S ρ
    let _ : MulDistribMulAction G (units k K S) := unitsAction S ρ
    let _ : Fintype (MulAction.orbitRel.Quotient G S) := Fintype.ofFinite _
    ∃ hU : HerbrandQuotientDefined G (units k K S) σ,
      let _ : Finite (HerbrandH0 G (units k K S)) := hU.1
      let _ : Finite (HerbrandHMinusOne G (units k K S) σ) := hU.2
      herbrandQuotient (G := G) (A := units k K S) σ =
        (∏ ω : MulAction.orbitRel.Quotient G S,
          (Nat.card (permutationOrbitStabilizer ω) : ℚ)) / (Nat.card G : ℚ) := by
  intro hPlace hUnits hOrbits
  have : IsCurveOver k K := FunctionField.isCurveOver k K
  let : MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := latticeAction S ρ
  obtain ⟨hL, hformula⟩ := lattice_herbrandQuotient S hS ρ σ hgen
  obtain ⟨hU, hcompare⟩ := herbrandQuotient_eq_lattice S ρ σ hgen hL
  refine ⟨hU, ?_⟩
  intro hU0 hUm
  exact hcompare.trans hformula

end FunctionField.SUnits
