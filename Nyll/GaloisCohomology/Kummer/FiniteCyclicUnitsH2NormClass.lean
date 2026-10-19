/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.FiniteGaloisTowerBaseUnitsH2Naturality
import Nyll.GaloisCohomology.ProP.FiniteCyclicH2PullbackNorm
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Cyclic unit H² classes and norms after base change

Every unit H² class is represented by a single base-field unit. A norm
preimage of that unit in a cyclic relative extension kills the restricted
inflation of its class.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K M : Type) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsCyclic Gal(M/K)]

/-- The actual unit H² class with the specified base-unit carry coefficient. -/
def finiteCyclicBaseUnitH2Class (g : Gal(M/K))
    (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2 := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let a₀ : LinearMap.ker
      (Rep.applyAsHom (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g - 𝟙 _).hom.toLinearMap :=
    ⟨Additive.ofMul a, by
      change Additive.ofMul a - Additive.ofMul a = 0
      exact sub_self _⟩
  exact finiteGaloisBaseUnitsH2Map K M
    (groupCohomology.H2π (Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (finiteCyclicCarryTwoCocycle (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g hg a₀))

/-- Every actual cyclic unit H² class has a single base-unit representative. -/
theorem finiteCyclicBaseUnitH2Class_surjective
    [IsGalois K M]
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) :
    Function.Surjective (finiteCyclicBaseUnitH2Class K M g hg) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  intro c
  obtain ⟨b, rfl⟩ := finiteCyclicBaseUnitsH2Map_surjective K M c
  obtain ⟨a, rfl⟩ := finiteCyclicGroupH2_piEven_surjective
    (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g hg b
  refine ⟨(show Additive Kˣ from a.1).toMul, ?_⟩
  exact congrArg (fun y => finiteGaloisBaseUnitsH2Map K M y)
    (H2π_finiteCyclicCarryTwoCocycle (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g hg a)

/-- A norm of the representing base unit kills the actual restricted inflation
in a cyclic relative Galois extension. -/
theorem finiteCyclicBaseUnitH2Class_inflation_restriction_eq_zero_of_norm
    (L N : Type) [Field L] [Field N]
    [Algebra K N] [Algebra K L] [Algebra L N] [IsScalarTower K L N]
    [Algebra M N] [IsScalarTower K M N] [Normal K M]
    [FiniteDimensional L N] [IsGalois L N] [IsCyclic Gal(N/L)]
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g)
    (a : Kˣ) (x : N) (hx : Algebra.norm L x = algebraMap K L (a : K)) :
    finiteGaloisTowerUnitsH2Restriction K L N
      (finiteGaloisTowerUnitsH2Inflation K M N (finiteCyclicBaseUnitH2Class K M g hg a)) = 0 := by
  classical
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let : CommGroup Gal(N/L) := IsCyclic.commGroup
  obtain ⟨h, hh⟩ := IsCyclic.exists_generator (α := Gal(N/L))
  let A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ)
  let B := Rep.ofAlgebraAutOnUnits L N
  let a₀ : LinearMap.ker (Rep.applyAsHom A g - 𝟙 _).hom.toLinearMap :=
    ⟨Additive.ofMul a, by
      change Additive.ofMul a - Additive.ofMul a = 0
      exact sub_self _⟩
  let c := groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a₀)
  let f : Gal(N/L) →* Gal(M/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp (AlgEquiv.restrictScalarsHom K)
  let φ : Rep.res f A ⟶ B := finiteTowerBaseUnitsRepHom K L N
  have hx0 : x ≠ 0 := by
    intro hz
    have ha0 := (algebraMap K L).injective.ne a.ne_zero
    apply ha0
    rw [← hx, hz, Algebra.norm_zero, map_zero]
  let b : B := Additive.ofMul (Units.mk0 x hx0)
  have hb : B.norm.hom b = φ.hom a₀.1 := by
    apply Units.ext
    change ((Additive.toMul ((Rep.ofAlgebraAutOnUnits L N).norm.hom
      (Additive.ofMul (Units.mk0 x hx0))) : Nˣ) : N) =
        algebraMap L N (algebraMap K L (a : K))
    exact (groupCohomology.norm_ofAlgebraAutOnUnits_eq
      (K := L) (L := N) (Units.mk0 x hx0)).trans (congrArg (algebraMap L N) hx)
  have hz : groupCohomology.map f φ 2 c = 0 :=
    finiteCyclicCarry_pullbackMap_eq_zero_of_norm A B g hg h hh f φ a₀ b hb
  have hnat := finiteGaloisTowerBaseUnitsH2_inflation_restriction K N L M
  have hcomp := groupCohomology.map_comp
    (A := A) (B := Rep.trivial ℤ Gal(N/L) (Additive Kˣ)) (C := B)
    f (MonoidHom.id Gal(N/L)) (𝟙 (Rep.trivial ℤ Gal(N/L) (Additive Kˣ)))
    (finiteTowerBaseUnitsRepHom K L N) 2
  have hmap : groupCohomology.map f φ 2 =
      groupCohomology.map f (𝟙 (Rep.trivial ℤ Gal(N/L) (Additive Kˣ))) 2 ≫
        finiteTowerBaseUnitsH2Map K L N := by
    refine (groupCohomology.map_congr (by ext σ; rfl) ?_ 2).trans hcomp
    apply LinearMap.ext
    intro y
    rfl
  have hnateval := congrArg
    (fun (m : groupCohomology A 2 ⟶ groupCohomology B 2) => m c) hnat
  have hmapeval := congrArg
    (fun (m : groupCohomology A 2 ⟶ groupCohomology B 2) => m c) hmap
  exact hnateval.trans (hmapeval.symm.trans hz)

end
end ClassFieldTower.Cohomology
