/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.LiftedCyclicUnitsH2Norm
public import Nyll.GaloisCohomology.Kummer.LiftedFiniteGaloisTowerUnitsH2
public import Nyll.GaloisCohomology.ProP.FiniteCyclicH2PullbackNorm
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryRestriction
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Base change of actual cyclic unit norm classes

The coefficient map is the original upper-field unit inclusion and the group map
is actual restriction. The same carry coefficient is killed by an actual relative
norm, and injective restriction gives the converse with a normalized generator.
-/

@[expose] public section

universe u v w
open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K : Type v) (M : Type u) (E : Type w) (N : Type u)
  [Field K] [Field M] [Field E] [Field N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [Normal K M]

/-- The actual composite unit coefficient map for inflation followed by restriction. -/
def liftedTowerUnitsBaseChangeRepHom :
    Rep.res ((AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp
      (AlgEquiv.restrictScalarsHom K)) (liftedGaloisUnitsRep K M) ⟶
        liftedGaloisUnitsRep E N :=
  (Rep.resFunctor (AlgEquiv.restrictScalarsHom K : Gal(N/E) →* Gal(N/K))).map
      (liftedFiniteGaloisTowerUnitsInflationRepHom K M N) ≫
    liftedFiniteGaloisTowerUnitsRestrictionRepHom K E N

/-- The actual field-tower composite is the cohomology map of the same composite data. -/
theorem liftedTowerUnitsH2BaseChange_eq :
    liftedFiniteGaloisTowerUnitsH2Inflation K M N ≫
        liftedFiniteGaloisTowerUnitsH2Restriction K E N =
      groupCohomology.map
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp
          (AlgEquiv.restrictScalarsHom K))
        (liftedTowerUnitsBaseChangeRepHom K M E N) 2 :=
  (groupCohomology.map_comp
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M)
    (AlgEquiv.restrictScalarsHom K : Gal(N/E) →* Gal(N/K))
    (liftedFiniteGaloisTowerUnitsInflationRepHom K M N)
    (liftedFiniteGaloisTowerUnitsRestrictionRepHom K E N) 2).symm

variable [FiniteDimensional K M] [IsCyclic Gal(M/K)]
  [FiniteDimensional E N] [IsCyclic Gal(N/E)]

/-- An actual relative field norm kills the restricted inflation of its base-unit class. -/
theorem liftedCyclicBaseUnitH2Class_inflation_restriction_eq_zero_of_norm
    [IsGalois E N]
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g)
    (a : Kˣ) (x : N) (hx : Algebra.norm E x = algebraMap K E (a : K)) :
    liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (liftedFiniteGaloisTowerUnitsH2Inflation K M N
        (liftedCyclicBaseUnitH2Class K M g hg a)) = 0 := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let : CommGroup Gal(N/E) := IsCyclic.commGroup
  obtain ⟨h, hh⟩ := IsCyclic.exists_generator (α := Gal(N/E))
  let A := liftedGaloisUnitsRep K M
  let B := liftedGaloisUnitsRep E N
  let f : Gal(N/E) →* Gal(M/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp (AlgEquiv.restrictScalarsHom K)
  let φ : Rep.res f A ⟶ B := liftedTowerUnitsBaseChangeRepHom K M E N
  let a₀ := liftedBaseUnitCycle K M g a
  let c := groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a₀)
  have hx0 : x ≠ 0 := by
    intro hz
    have ha0 := (algebraMap K E).injective.ne a.ne_zero
    apply ha0
    rw [← hx, hz, Algebra.norm_zero, map_zero]
  let b : B := Additive.ofMul (Units.mk0 x hx0)
  have hb : B.norm.asHom.hom b = φ.hom a₀.val := by
    apply Units.ext
    change ((Additive.toMul ((liftedGaloisUnitsRep E N).norm.asHom.hom
      (Additive.ofMul (Units.mk0 x hx0))) : Nˣ) : N) =
        algebraMap M N (algebraMap K M (a : K))
    exact (liftedGaloisUnits_norm_eq E N (Units.mk0 x hx0)).trans
      ((congrArg (algebraMap E N) hx).trans
        ((IsScalarTower.algebraMap_apply K E N (a : K)).symm.trans
          (IsScalarTower.algebraMap_apply K M N (a : K))))
  have hz : groupCohomology.map f φ 2 c = 0 :=
    finiteCyclicCarry_pullbackMap_eq_zero_of_norm A B g hg h hh f φ a₀ b hb
  have he := congrArg
    (fun (m : groupCohomology A 2 ⟶ groupCohomology B 2) => m c)
    (liftedTowerUnitsH2BaseChange_eq K M E N)
  exact he.trans hz

/-- Index-normalized relative generators preserve the actual representing base unit. -/
theorem liftedCyclicBaseUnitH2Class_inflation_restriction_eq_class
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g)
    (h : Gal(N/E)) (hh : ∀ σ : Gal(N/E), σ ∈ Subgroup.zpowers h)
    (d : ℕ) (hd : 0 < d) (hcard : Nat.card Gal(M/K) = d * Nat.card Gal(N/E))
    (hgen : (h.restrictScalars K).restrictNormal M = g ^ d) (a : Kˣ) :
    liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (liftedFiniteGaloisTowerUnitsH2Inflation K M N
        (liftedCyclicBaseUnitH2Class K M g hg a)) =
      liftedCyclicBaseUnitH2Class E N h hh (Units.map (algebraMap K E).toMonoidHom a) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let : CommGroup Gal(N/E) := IsCyclic.commGroup
  let A := liftedGaloisUnitsRep K M
  let B := liftedGaloisUnitsRep E N
  let f : Gal(N/E) →* Gal(M/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp (AlgEquiv.restrictScalarsHom K)
  let φ : Rep.res f A ⟶ B := liftedTowerUnitsBaseChangeRepHom K M E N
  let a₀ := liftedBaseUnitCycle K M g a
  let b₀ := liftedBaseUnitCycle E N h (Units.map (algebraMap K E).toMonoidHom a)
  have hab : φ.hom a₀.val = b₀.val := by
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply K M N (a : K)).symm.trans
      (IsScalarTower.algebraMap_apply K E N (a : K))
  have hcarry := finiteCyclicCarry_mapCocycles₂_of_generator_power
    A B g hg h hh f φ d hd hcard hgen a₀ b₀ hab
  have hclass := groupCohomology.H2π_comp_map_apply f φ
    (finiteCyclicCarryTwoCocycle A g hg a₀)
  rw [hcarry] at hclass
  let c := groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a₀)
  have he := congrArg
    (fun (m : groupCohomology A 2 ⟶ groupCohomology B 2) => m c)
    (liftedTowerUnitsH2BaseChange_eq K M E N)
  exact he.trans hclass

/-- Injective actual restriction identifies vanishing with the original relative norm equation. -/
theorem liftedCyclicBaseUnitH2Class_baseChange_eq_zero_iff_norm
    [IsGalois E N]
    (hinj : Function.Injective
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp
        (AlgEquiv.restrictScalarsHom K : Gal(N/E) →* Gal(N/K))))
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (liftedFiniteGaloisTowerUnitsH2Inflation K M N
        (liftedCyclicBaseUnitH2Class K M g hg a)) = 0 ↔
      ∃ x : N, Algebra.norm E x = algebraMap K E (a : K) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let f : Gal(N/E) →* Gal(M/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp (AlgEquiv.restrictScalarsHom K)
  obtain ⟨h, hh, hgen, hcard⟩ := finiteCyclic_exists_generator_map_index g hg f hinj
  have hclass := liftedCyclicBaseUnitH2Class_inflation_restriction_eq_class
    K M E N g hg h hh f.range.index (Nat.pos_of_ne_zero f.range.index_ne_zero_of_finite)
    hcard hgen a
  have heq :
      (liftedFiniteGaloisTowerUnitsH2Restriction K E N
        (liftedFiniteGaloisTowerUnitsH2Inflation K M N
          (liftedCyclicBaseUnitH2Class K M g hg a)) = 0) ↔
      (liftedCyclicBaseUnitH2Class E N h hh (Units.map (algebraMap K E).toMonoidHom a) = 0) :=
    ⟨fun hz => hclass.symm.trans hz, fun hz => hclass.trans hz⟩
  exact heq.trans (liftedCyclicBaseUnitH2Class_eq_zero_iff_norm E N h hh
    (Units.map (algebraMap K E).toMonoidHom a))

end
end ClassFieldTower.Cohomology
