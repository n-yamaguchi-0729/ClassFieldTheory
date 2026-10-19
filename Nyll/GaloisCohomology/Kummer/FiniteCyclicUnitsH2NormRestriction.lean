/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormClass
import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormCriterion
import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryRestriction

/-!
# Restriction of a cyclic norm class with a normalized relative generator

The actual restricted inflation of the base-unit class is the class of the
same unit over the new base field. The generator maps to the index power;
the carry-coordinate comparison supplies the equality of cocycles.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

/-- With the relative generator normalized by the subgroup index, restriction
preserves the representing base unit. -/
theorem finiteCyclicBaseUnitH2Class_inflation_restriction_eq_class
    (K M E N : Type) [Field K] [Field M] [Field E] [Field N]
    [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
    [IsScalarTower K M N] [IsScalarTower K E N] [Normal K M]
    [FiniteDimensional K M] [IsCyclic Gal(M/K)]
    [FiniteDimensional E N] [IsCyclic Gal(N/E)]
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g)
    (h : Gal(N/E)) (hh : ∀ σ : Gal(N/E), σ ∈ Subgroup.zpowers h)
    (d : ℕ) (hd : 0 < d) (hcard : Nat.card Gal(M/K) = d * Nat.card Gal(N/E))
    (hgen : ((h.restrictScalars K).restrictNormal M) = g ^ d) (a : Kˣ) :
    finiteGaloisTowerUnitsH2Restriction K E N
      (finiteGaloisTowerUnitsH2Inflation K M N (finiteCyclicBaseUnitH2Class K M g hg a)) =
        finiteCyclicBaseUnitH2Class E N h hh (Units.map (algebraMap K E).toMonoidHom a) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let : CommGroup Gal(N/E) := IsCyclic.commGroup
  let A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ)
  let T := Rep.trivial ℤ Gal(N/E) (Additive Eˣ)
  let B := Rep.ofAlgebraAutOnUnits E N
  let f : Gal(N/E) →* Gal(M/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp (AlgEquiv.restrictScalarsHom K)
  let ψ : Rep.res f A ⟶ T := (Rep.trivialFunctor ℤ Gal(N/E)).map
    (ModuleCat.ofHom (Units.map (algebraMap K E).toMonoidHom).toAdditive.toIntLinearMap)
  let a₀ : LinearMap.ker (Rep.applyAsHom A g - 𝟙 _).hom.toLinearMap :=
    ⟨Additive.ofMul a, by
      change Additive.ofMul a - Additive.ofMul a = 0
      exact sub_self _⟩
  let b₀ : LinearMap.ker (Rep.applyAsHom T h - 𝟙 _).hom.toLinearMap :=
    ⟨Additive.ofMul (Units.map (algebraMap K E).toMonoidHom a), by
      change Additive.ofMul (Units.map (algebraMap K E).toMonoidHom a) -
        Additive.ofMul (Units.map (algebraMap K E).toMonoidHom a) = 0
      exact sub_self _⟩
  let c := groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a₀)
  have hcarry := finiteCyclicCarry_mapCocycles₂_of_generator_power
    A T g hg h hh f ψ d hd hcard hgen a₀ b₀ rfl
  have hclass := groupCohomology.H2π_comp_map_apply f ψ
    (finiteCyclicCarryTwoCocycle A g hg a₀)
  rw [hcarry] at hclass
  let φ : Rep.res f A ⟶ B := finiteTowerBaseUnitsRepHom K E N
  have hnat := finiteGaloisTowerBaseUnitsH2_inflation_restriction K N E M
  have hcomp₁ := groupCohomology.map_comp
    (A := A) (B := Rep.trivial ℤ Gal(N/E) (Additive Kˣ)) (C := B)
    f (MonoidHom.id Gal(N/E)) (𝟙 (Rep.trivial ℤ Gal(N/E) (Additive Kˣ))) φ 2
  have hcomp₂ := groupCohomology.map_comp
    (A := A) (B := T) (C := B) f (MonoidHom.id Gal(N/E)) ψ
    (finiteGaloisBaseUnitsRepHom E N) 2
  have hfirst : groupCohomology.map f φ 2 =
      groupCohomology.map f (𝟙 (Rep.trivial ℤ Gal(N/E) (Additive Kˣ))) 2 ≫
        finiteTowerBaseUnitsH2Map K E N := by
    refine (groupCohomology.map_congr (by ext σ; rfl) ?_ 2).trans hcomp₁
    apply LinearMap.ext
    intro y
    rfl
  have hsecond : groupCohomology.map f φ 2 =
      groupCohomology.map f ψ 2 ≫ finiteGaloisBaseUnitsH2Map E N := by
    refine (groupCohomology.map_congr (by ext σ; rfl) ?_ 2).trans hcomp₂
    apply LinearMap.ext
    intro y
    rfl
  have hnateval := congrArg
    (fun (m : groupCohomology A 2 ⟶ groupCohomology B 2) => m c) hnat
  have hfirsteval := congrArg
    (fun (m : groupCohomology A 2 ⟶ groupCohomology B 2) => m c) hfirst
  have hsecondeval := congrArg
    (fun (m : groupCohomology A 2 ⟶ groupCohomology B 2) => m c) hsecond
  exact hnateval.trans (hfirsteval.symm.trans (hsecondeval.trans
    (congrArg (fun z => finiteGaloisBaseUnitsH2Map E N z) hclass)))

/-- An injective restriction of Galois groups identifies vanishing of a
base-changed cyclic class with an actual relative field norm. -/
theorem finiteCyclicBaseUnitH2Class_baseChange_eq_zero_iff_norm
    (K M E N : Type) [Field K] [Field M] [Field E] [Field N]
    [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
    [IsScalarTower K M N] [IsScalarTower K E N] [Normal K M]
    [FiniteDimensional K M] [IsCyclic Gal(M/K)]
    [FiniteDimensional E N] [IsGalois E N] [IsCyclic Gal(N/E)]
    (hinj : Function.Injective
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp
        (AlgEquiv.restrictScalarsHom K : Gal(N/E) →* Gal(N/K))))
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    finiteGaloisTowerUnitsH2Restriction K E N
      (finiteGaloisTowerUnitsH2Inflation K M N (finiteCyclicBaseUnitH2Class K M g hg a)) = 0 ↔
        ∃ x : N, Algebra.norm E x = algebraMap K E (a : K) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let f : Gal(N/E) →* Gal(M/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp (AlgEquiv.restrictScalarsHom K)
  obtain ⟨h, hh, hgen, hcard⟩ := finiteCyclic_exists_generator_map_index g hg f hinj
  have hclass := finiteCyclicBaseUnitH2Class_inflation_restriction_eq_class
    K M E N g hg h hh f.range.index (Nat.pos_of_ne_zero f.range.index_ne_zero_of_finite)
    hcard hgen a
  have heq :
      (finiteGaloisTowerUnitsH2Restriction K E N
        (finiteGaloisTowerUnitsH2Inflation K M N (finiteCyclicBaseUnitH2Class K M g hg a)) = 0) ↔
      (finiteCyclicBaseUnitH2Class E N h hh (Units.map (algebraMap K E).toMonoidHom a) = 0) :=
    ⟨fun hz => hclass.symm.trans hz, fun hz => hclass.trans hz⟩
  exact heq.trans (finiteCyclicBaseUnitH2Class_eq_zero_iff_norm E N h hh
    (Units.map (algebraMap K E).toMonoidHom a))

end
end ClassFieldTower.Cohomology
