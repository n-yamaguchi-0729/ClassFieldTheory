/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.Algebra.Brauer.EmbeddedInflation
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryRestriction

/-! # Restriction of actual cyclic Brauer classes -/

@[expose] public section

noncomputable section

open CategoryTheory ClassFieldTower.Cohomology

namespace ClassFieldTheory.Brauer

universe u

variable {K F M : Type u} [Field K] [Field F] [Field M]
    [Algebra K F] [Algebra F M] [Algebra K M] [IsScalarTower K F M]
    [FiniteDimensional F M] [IsGalois F M]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [IsCyclic Gal(E/K)] [IsCyclic Gal(M/F)]

/-- Under the actual relative restriction, the normalized subgroup generator
gives the carry of the original image of the base unit. -/
theorem embeddedRelativeRestriction_cyclicContinuousUnitClass (j : E →ₐ[K] M)
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g)
    (h : Gal(M/F)) (hh : ∀ σ : Gal(M/F), σ ∈ Subgroup.zpowers h)
    (d : ℕ) (hd : 0 < d) (hcard : Nat.card Gal(E/K) = d * Nat.card Gal(M/F))
    (hgen : embeddedGaloisRestriction (B := F) j h = g ^ d) (a : Kˣ) :
    embeddedRelativeRestriction E j (cyclicContinuousUnitClass K E g hg (Additive.ofMul a)) =
      cyclicContinuousUnitClass F M h hh
        (Additive.ofMul (Units.map (algebraMap K F).toMonoidHom a)) := by
  let : CommGroup Gal(E/K) := IsCyclic.commGroup
  let : CommGroup Gal(M/F) := IsCyclic.commGroup
  let r := embeddedGaloisRestriction (B := F) j
  let hr := embeddedGaloisRestriction_commutes (B := F) j
  let φ := liftedGaloisUnitsMap r j.toRingHom hr
  let b := Units.map (algebraMap K F).toMonoidHom a
  apply (continuousRelativeUnitsH2Equiv F M).injective
  change continuousRelativeUnitsH2Equiv F M
      ((ContinuousCohomology.map r (galoisUnitsMap r j.toRingHom hr) 2)
        ((continuousRelativeUnitsH2Equiv K E).symm (cyclicUnitClass K E g hg (Additive.ofMul a)))) =
    continuousRelativeUnitsH2Equiv F M
      ((continuousRelativeUnitsH2Equiv F M).symm (cyclicUnitClass F M h hh (Additive.ofMul b)))
  rw [continuousRelativeUnitsH2Equiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let A := liftedGaloisUnitsRep K E
  let B := liftedGaloisUnitsRep F M
  let a₀ := liftedBaseUnitCycle K E g a
  let b₀ := liftedBaseUnitCycle F M h b
  have hab : φ.hom a₀.val = b₀.val := by
    let u : Additive Eˣ := a₀.val
    have hcoeff : φ.hom a₀.val = Additive.ofMul (Units.map j.toMonoidHom u.toMul) :=
      liftedGaloisUnitsMap_apply r j.toRingHom hr u
    refine hcoeff.trans ?_
    apply Additive.ofMul.injective
    apply Units.ext
    change j (algebraMap K E (a : K)) = algebraMap F M (algebraMap K F (a : K))
    rw [j.commutes, IsScalarTower.algebraMap_apply K F M]
  change groupCohomology.map r.toMonoidHom φ 2
      (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a₀)) =
    groupCohomology.H2π B (finiteCyclicCarryTwoCocycle B h hh b₀)
  rw [groupCohomology.H2π_comp_map_apply,
    finiteCyclicCarry_mapCocycles₂_of_generator_power
      A B g hg h hh r.toMonoidHom φ d hd hcard hgen a₀ b₀ hab]

/-- The same carry calculation gives canonical absolute restriction to a
splitting stage embedded in the separable closure of the completed base. -/
theorem restrict_cyclicBrauerClass_eq_cyclicBrauerClass
    (N : FiniteGaloisIntermediateField F (SeparableClosure F)) [Algebra K N] [IsScalarTower K F N]
    [IsCyclic Gal(N/F)] (j : E →ₐ[K] N)
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g)
    (h : Gal(N/F)) (hh : ∀ σ : Gal(N/F), σ ∈ Subgroup.zpowers h)
    (d : ℕ) (hd : 0 < d) (hcard : Nat.card Gal(E/K) = d * Nat.card Gal(N/F))
    (hgen : embeddedGaloisRestriction (B := F) j h = g ^ d) (a : Kˣ) :
    restrict (algebraMap K F) (cyclicBrauerClass E g hg a) =
      cyclicBrauerClass N h hh (Units.map (algebraMap K F).toMonoidHom a) := by
  unfold cyclicBrauerClass
  rw [restrict_finiteInflation_eq_finiteInflation_embeddedRelativeRestriction E N j,
    embeddedRelativeRestriction_cyclicContinuousUnitClass E j g hg h hh d hd hcard hgen a]

end ClassFieldTheory.Brauer
