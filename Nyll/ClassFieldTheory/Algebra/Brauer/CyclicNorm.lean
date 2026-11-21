/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Nyll.ClassFieldTheory.Algebra.Brauer.DiscreteRelative
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteInflation
public import Nyll.GaloisCohomology.Kummer.LiftedCyclicUnitsH2Norm
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryInflation
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

/-! # The unit class in cyclic degree-two cohomology -/

@[expose] public section

noncomputable section

open CategoryTheory ClassFieldTower.Cohomology LocalFieldTheory TopRep

namespace ClassFieldTheory.Brauer

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)

/-- The actual degree-two carry class of a base unit is additive. -/
def cyclicUnitClass : Additive Kˣ →+ groupCohomology (liftedGaloisUnitsRep K L) 2 := by
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  refine
    { toFun := fun a => liftedCyclicBaseUnitH2Class K L g hg a.toMul
      map_zero' := ?_
      map_add' := ?_ }
  · apply (liftedCyclicBaseUnitH2Class_eq_zero_iff_norm K L g hg 1).mpr
    exact ⟨1, map_one (Algebra.norm K : L →* K)⟩
  · intro a b
    change liftedCyclicBaseUnitH2Class K L g hg (a.toMul * b.toMul) =
      liftedCyclicBaseUnitH2Class K L g hg a.toMul + liftedCyclicBaseUnitH2Class K L g hg b.toMul
    simp only [liftedCyclicBaseUnitH2Class_eq_piEven]
    let π₂ := Rep.FiniteCyclicGroup.groupCohomologyπEven
      (liftedGaloisUnitsRep K L) g hg 2 (by decide)
    have h (x : Kˣ) : (↑(liftedBaseUnitCycle K L g x) : liftedGaloisUnitsRep K L) =
        Additive.ofMul (α := Lˣ) (Units.map (algebraMap K L).toMonoidHom x) := rfl
    have hab : liftedBaseUnitCycle K L g (a.toMul * b.toMul) =
        liftedBaseUnitCycle K L g a.toMul + liftedBaseUnitCycle K L g b.toMul := by
      apply Subtype.ext
      change (liftedBaseUnitCycle K L g (a.toMul * b.toMul)).val =
        (liftedBaseUnitCycle K L g a.toMul).val + (liftedBaseUnitCycle K L g b.toMul).val
      rw [h, h, h]
      exact congrArg Additive.ofMul
        (map_mul (Units.map (algebraMap K L).toMonoidHom) a.toMul b.toMul)
    exact (congrArg (fun z => π₂ z) hab).trans (π₂.hom.map_add _ _)

/-- The same carry class in continuous relative cohomology. -/
def cyclicContinuousUnitClass : Additive Kˣ →+ continuousCohomology 2 (galoisUnitsRep K L) :=
  (continuousRelativeUnitsH2Equiv K L).symm.toAddMonoidHom.comp (cyclicUnitClass K L g hg)

/-- Changing the chosen generator retains the same base unit and acts by
the coordinate of the new generator in the old character. -/
theorem cyclicContinuousUnitClass_changeGenerator
    (h : Gal(L/K)) (hh : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers h) (a : Kˣ) :
    cyclicContinuousUnitClass K L g hg (Additive.ofMul a) =
      (finiteCyclicGeneratorCoordinate g hg h).val •
        cyclicContinuousUnitClass K L h hh (Additive.ofMul a) := by
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let e := continuousRelativeUnitsH2Equiv K L
  apply e.injective
  rw [map_nsmul]
  change e (e.symm (cyclicUnitClass K L g hg (Additive.ofMul a))) =
    (finiteCyclicGeneratorCoordinate g hg h).val •
      e (e.symm (cyclicUnitClass K L h hh (Additive.ofMul a)))
  rw [e.apply_symm_apply, e.apply_symm_apply]
  exact finiteCyclicCarry_changeGenerator_eq_nsmul (liftedGaloisUnitsRep K L)
    g hg h hh (liftedBaseUnitCycle K L g a) (liftedBaseUnitCycle K L h a) rfl

/-- A cyclic carry class vanishes exactly at norms of actual upper-field units. -/
theorem cyclicUnitClass_eq_zero_iff_norm (a : Kˣ) :
    cyclicUnitClass K L g hg (Additive.ofMul a) = 0 ↔ a ∈ localNormSubgroup K L := by
  change liftedCyclicBaseUnitH2Class K L g hg a = 0 ↔ a ∈ localNormSubgroup K L
  rw [liftedCyclicBaseUnitH2Class_eq_zero_iff_norm]
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro h
      apply a.ne_zero
      rw [← hx, h, Algebra.norm_zero]
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨(x : L), congrArg Units.val hx⟩

/-- Every cyclic degree-two field-unit class has a base-unit representative. -/
theorem cyclicUnitClass_surjective : Function.Surjective (cyclicUnitClass K L g hg) := by
  intro x
  obtain ⟨a, ha⟩ := liftedCyclicBaseUnitH2Class_surjective K L g hg x
  exact ⟨Additive.ofMul a, ha⟩

/-- Cyclic degree-two cohomology is the quotient by the original field norms. -/
def cyclicUnitH2NormEquiv :
    groupCohomology (liftedGaloisUnitsRep K L) 2 ≃+ Additive (NormQuotient K L) := by
  let q := (normClass K L).toAdditive
  have hq : Function.Surjective q := by
    intro x
    refine NormQuotient.inductionOn (motive := fun y => ∃ a : Additive Kˣ, q a = Additive.ofMul y)
      x.toMul ?_
    exact fun a => ⟨Additive.ofMul a, rfl⟩
  have hker : (cyclicUnitClass K L g hg).ker = q.ker := by
    ext a
    change cyclicUnitClass K L g hg (Additive.ofMul a.toMul) = 0 ↔ normClass K L a.toMul = 1
    rw [cyclicUnitClass_eq_zero_iff_norm, normClass_eq_one_iff_mem]
  exact (QuotientAddGroup.quotientKerEquivOfSurjective (cyclicUnitClass K L g hg)
    (cyclicUnitClass_surjective K L g hg)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective q hq))

/-- The cyclic carry class of the original unit inflated to the absolute
Brauer group through the specified finite Galois stage. -/
def cyclicBrauerClass {K : Type u} [Field K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [IsCyclic Gal(E/K)]
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) : Br K :=
  finiteInflation E (cyclicContinuousUnitClass K E g hg (Additive.ofMul a))

end ClassFieldTheory.Brauer
