/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.Kummer.UnitsPrimitiveDescent
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Injectivity of lifted field-unit inflation

The original actual-unit primitive descent applies without changing the units or
Galois action. Only the coefficient scalar ring used to form H² is lifted.
-/

@[expose] public section

universe u v

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L) [Normal K E]

/-- Lifted inflation is the actual pullback of arguments and inclusion of units. -/
theorem liftedFiniteGaloisUnitsH2Inflation_H2π
    (c : groupCohomology.cocycles₂ (liftedGaloisUnitsRep K E)) :
    (liftedFiniteGaloisUnitsH2Inflation K L E).hom
        (groupCohomology.H2π (liftedGaloisUnitsRep K E) c) =
      groupCohomology.H2π (liftedGaloisUnitsRep K L)
        (groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom E)
          (liftedFiniteGaloisUnitsInflationRepHom K L E) c) := by
  exact congrArg (fun f => f c)
    (groupCohomology.H2π_comp_map (AlgEquiv.restrictNormalHom E)
      (liftedFiniteGaloisUnitsInflationRepHom K L E))

/-- The same Hilbert 90 correction proves injectivity in the original field universe. -/
theorem liftedFiniteGaloisUnitsH2Inflation_injective
    [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (liftedFiniteGaloisUnitsH2Inflation K L E).hom := by
  have hzero : ∀ x : groupCohomology (liftedGaloisUnitsRep K E) 2,
      (liftedFiniteGaloisUnitsH2Inflation K L E).hom x = 0 → x = 0 := by
    intro x
    induction x using groupCohomology.H2_induction_on with
    | h c =>
      intro hx
      rw [liftedFiniteGaloisUnitsH2Inflation_H2π] at hx
      obtain ⟨b, hb⟩ := (groupCohomology.H2π_eq_zero_iff _).mp hx
      let b₀ : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L := b
      have hb' (σ τ : Gal(L/K)) :
          (Rep.ofAlgebraAutOnUnits K L).ρ σ (b₀ τ) - b₀ (σ * τ) + b₀ σ =
            unitsInclusion K L E
              (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)) :=
        congrFun hb (σ, τ)
      obtain ⟨a, ha⟩ := unitsPrimitiveDescends K L E c
        (groupCohomology.cocycles₂_map_one_snd c)
        (groupCohomology.cocycles₂_map_one_fst c) b₀ hb'
      exact (groupCohomology.H2π_eq_zero_iff c).mpr
        ⟨a, funext (fun στ => ha στ.1 στ.2)⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [map_sub, hxy, sub_self]

end
end ClassFieldTower.Cohomology
