/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.Cyclic.Herbrand.FieldUnits
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Nyll.GaloisCohomology.ProP.FiniteCyclicBarPeriodicH2Comparison
public import Nyll.GaloisCohomology.ProP.FiniteCyclicH2CoefficientNorm
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Norm.Basic

/-!
# Actual cyclic unit norm classes with lifted integer coefficients

The coefficient of the carry cocycle is the original base-field unit embedded into the
original upper field. The existing lifted representation keeps these units and their
Galois action unchanged. Its periodic representative vanishes exactly when that same
base-field unit is an actual field norm.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace ClassFieldTower.Cohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K : Type v) (M : Type u) [Field K] [Field M] [Algebra K M]

/-- A base unit is fixed by the actual generator acting on the original upper-field units. -/
def liftedBaseUnitCycle (g : Gal(M/K)) (a : Kˣ) :
    LinearMap.ker ((liftedGaloisUnitsRep K M).ρ g - LinearMap.id) :=
  ⟨Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a), by
    change (liftedGaloisUnitsRep K M).ρ g
      (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a)) -
        (show liftedGaloisUnitsRep K M from
          Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a)) = 0
    apply sub_eq_zero.mpr
    apply Units.ext
    exact g.commutes (a : K)⟩

variable [FiniteDimensional K M] [IsCyclic Gal(M/K)]

/-- The carry class of the same embedded base unit in the field's own universe. -/
def liftedCyclicBaseUnitH2Class (g : Gal(M/K))
    (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    groupCohomology (liftedGaloisUnitsRep K M) 2 := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  exact groupCohomology.H2π (liftedGaloisUnitsRep K M)
    (finiteCyclicCarryTwoCocycle (liftedGaloisUnitsRep K M) g hg
      (liftedBaseUnitCycle K M g a))

/-- The actual carry cocycle is the periodic class of its original coefficient. -/
theorem liftedCyclicBaseUnitH2Class_eq_piEven (g : Gal(M/K))
    (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    let _ : CommGroup Gal(M/K) := IsCyclic.commGroup
    liftedCyclicBaseUnitH2Class K M g hg a =
      Rep.FiniteCyclicGroup.groupCohomologyπEven (liftedGaloisUnitsRep K M)
        g hg 2 (by decide) (liftedBaseUnitCycle K M g a) := by
  intro sharedCommGroup
  exact H2π_finiteCyclicCarryTwoCocycle (liftedGaloisUnitsRep K M) g hg
    (liftedBaseUnitCycle K M g a)

variable [IsGalois K M]

/-- The original fixed-unit descent supplies a base-unit representative of every class. -/
theorem liftedCyclicBaseUnitH2Class_surjective (g : Gal(M/K))
    (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) :
    Function.Surjective (liftedCyclicBaseUnitH2Class K M g hg) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  intro c
  obtain ⟨a, rfl⟩ := finiteCyclicGroupH2_piEven_surjective (liftedGaloisUnitsRep K M) g hg c
  have hag : (liftedGaloisUnitsRep K M).ρ g a.val = a.val := by
    have hz := a.property
    change (liftedGaloisUnitsRep K M).ρ g a.val - a.val = 0 at hz
    exact sub_eq_zero.mp hz
  have hfixed : ∀ σ : Gal(M/K), (liftedGaloisUnitsRep K M).ρ σ a.val = a.val :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (liftedGaloisUnitsRep K M).ρ g hg a.val).mpr hag
  let x : fixedSubgroup Gal(M/K) Mˣ :=
    ⟨(show Additive Mˣ from a.val).toMul, fun σ =>
      congrArg (fun z : Additive Mˣ => z.toMul) (hfixed σ)⟩
  refine ⟨CyclicCohomology.fixedUnitsEquivBaseUnits K M x, ?_⟩
  rw [liftedCyclicBaseUnitH2Class_eq_piEven]
  apply congrArg (Rep.FiniteCyclicGroup.groupCohomologyπEven
    (liftedGaloisUnitsRep K M) g hg 2 (by decide))
  apply Subtype.ext
  change Units.map (algebraMap K M).toMonoidHom
    (CyclicCohomology.fixedUnitsEquivBaseUnits K M x) =
      (show Additive Mˣ from a.val).toMul
  apply Units.ext
  exact CyclicCohomology.fixedUnitsEquivBaseUnits_spec K M x

/-- Vanishing of this actual cyclic class is precisely the original field norm equation. -/
theorem liftedCyclicBaseUnitH2Class_eq_zero_iff_norm (g : Gal(M/K))
    (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    liftedCyclicBaseUnitH2Class K M g hg a = 0 ↔
      ∃ x : M, Algebra.norm K x = (a : K) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  rw [liftedCyclicBaseUnitH2Class_eq_piEven]
  refine (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    (liftedGaloisUnitsRep K M) g hg 2 (by decide)
      (liftedBaseUnitCycle K M g a)).trans ?_
  constructor
  · rintro ⟨b, hb⟩
    let x : Mˣ := (show Additive Mˣ from b).toMul
    refine ⟨(x : M), (algebraMap K M).injective ?_⟩
    have h := congrArg (fun z : liftedGaloisUnitsRep K M =>
      ((show Additive Mˣ from z).toMul : M)) hb
    exact (liftedGaloisUnits_norm_eq K M x).symm.trans h
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro hz
      apply a.ne_zero
      rw [← hx, hz, Algebra.norm_zero]
    refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
    apply Units.ext
    exact (liftedGaloisUnits_norm_eq K M (Units.mk0 x hx0)).trans
      (congrArg (algebraMap K M) hx)

end ClassFieldTower.Cohomology
