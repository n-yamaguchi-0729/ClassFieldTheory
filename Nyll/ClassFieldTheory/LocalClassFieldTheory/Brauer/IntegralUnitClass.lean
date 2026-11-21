/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.UnitsInvariants
public import Nyll.GaloisCohomology.Topology.ContinuousInvariantPairing

/-! # Integral cohomology classes with an invariant unit coefficient -/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

section IntegralCoefficients

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Discrete integer coefficients with their trivial action. -/
def trivialIntegralTopRep : TopRep.{u} ℤ G :=
  discreteCoefficientTopRep ℤ G (Rep.trivial ℤ G (ULift.{u} ℤ))

instance trivialIntegralTopRep_discrete : DiscreteTopology (trivialIntegralTopRep G) :=
  discreteCoefficientTopRep_discrete ℤ G (Rep.trivial ℤ G (ULift.{u} ℤ))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem trivialIntegralTopRep_ρ (σ : G) (a : trivialIntegralTopRep G) :
    (trivialIntegralTopRep G).ρ σ a = a := rfl

variable {G} {J : Type u} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- Restriction preserves the original integer coefficient. -/
def integralRestrictionCoefficient (r : J →ₜ* G) :
    TopRep.res r.toMonoidHom (trivialIntegralTopRep G) ⟶ trivialIntegralTopRep J := by
  let X := TopRep.res r.toMonoidHom (trivialIntegralTopRep G)
  let Y := trivialIntegralTopRep J
  change X ⟶ Y
  refine ConcreteCategory.ofHom (C := TopRep.{u} ℤ J) (X := X) (Y := Y)
    { toLinearMap := ?_, cont := ?_, isIntertwining' := ?_ }
  · exact { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  · have hdisc : @DiscreteTopology X X.hV3 := trivialIntegralTopRep_discrete G
    exact @continuous_of_discreteTopology X X.hV3 hdisc Y Y.hV3 _
  · intro σ
    rfl

/-- Pullback on the actual degree-two integer cohomology along a continuous group map. -/
def integralRestriction (r : J →ₜ* G) :
    continuousCohomology 2 (trivialIntegralTopRep G) →+
      continuousCohomology 2 (trivialIntegralTopRep J) :=
  (map r (integralRestrictionCoefficient r) 2).hom.toLinearMap.toAddMonoidHom

theorem integralRestriction_π (r : J →ₜ* G) (z : cocycles (trivialIntegralTopRep G) 2) :
    integralRestriction r (π (trivialIntegralTopRep G) 2 z) =
      π (trivialIntegralTopRep J) 2 (cocyclesMap r (integralRestrictionCoefficient r) 2 z) :=
  ConcreteCategory.congr_hom (π_map r (integralRestrictionCoefficient r) 2) z

end IntegralCoefficients

section IntegralUnits

variable (F : Type u) [Field F]

local notation "Gᶠ" => Gal(SeparableClosure F/F)

/-- The original integral action on the unit coefficients. -/
def unitScalarPairing : trivialIntegralTopRep Gᶠ →ₗ[ℤ] unitsRep F →ₗ[ℤ] unitsRep F :=
  (LinearMap.lsmul ℤ (unitsRep F)).comp (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap

theorem unitScalarPairing_continuous :
    Continuous (fun t : trivialIntegralTopRep Gᶠ × unitsRep F => unitScalarPairing F t.1 t.2) :=
  continuous_of_discreteTopology

theorem unitScalarPairing_equivariant (σ : Gᶠ) (a : trivialIntegralTopRep Gᶠ) (b : unitsRep F) :
    unitScalarPairing F ((trivialIntegralTopRep Gᶠ).ρ σ a) ((unitsRep F).ρ σ b) =
      (unitsRep F).ρ σ (unitScalarPairing F a b) := by
  rw [trivialIntegralTopRep_ρ]
  change (show ULift.{u} ℤ from a).down • (unitsRep F).ρ σ b =
    (unitsRep F).ρ σ ((show ULift.{u} ℤ from a).down • b)
  exact (map_smul ((unitsRep F).ρ σ) _ _).symm

/-- The original intertwiner sends an integer to that power of the given field unit. -/
def unitScalarCoefficientMap (b : Fˣ) : trivialIntegralTopRep Gᶠ ⟶ unitsRep F :=
  rightInvariantCoefficientMap (unitScalarPairing F) (unitScalarPairing_continuous F)
    (unitScalarPairing_equivariant F) (baseUnitInvariant F b)

theorem unitScalarCoefficientMap_apply (b : Fˣ) (a : trivialIntegralTopRep Gᶠ) :
    unitScalarCoefficientMap F b a =
      (show ULift.{u} ℤ from a).down •
        (show unitsRep F from Additive.ofMul (α := (SeparableClosure F)ˣ)
          (Units.map (algebraMap F (SeparableClosure F)).toMonoidHom b)) :=
  rfl

/-- Cup with a field unit sends a degree-two integer class to the actual Brauer group. -/
def unitsIntegralClass (b : Fˣ) : continuousCohomology 2 (trivialIntegralTopRep Gᶠ) →+ Br F :=
  (map (ContinuousMonoidHom.id Gᶠ) (unitScalarCoefficientMap F b) 2).hom.toLinearMap.toAddMonoidHom

theorem unitsIntegralClass_π (b : Fˣ) (z : cocycles (trivialIntegralTopRep Gᶠ) 2) :
    unitsIntegralClass F b (π (trivialIntegralTopRep Gᶠ) 2 z) =
      π (unitsRep F) 2
        (cocyclesMap (ContinuousMonoidHom.id Gᶠ) (unitScalarCoefficientMap F b) 2 z) := by
  let X := trivialIntegralTopRep Gᶠ
  let Y := unitsRep F
  let i := ContinuousMonoidHom.id Gᶠ
  let m : TopRep.res i.toMonoidHom X ⟶ Y := unitScalarCoefficientMap F b
  exact ConcreteCategory.congr_hom (π_map (X := X) (Y := Y) i m 2) z

end IntegralUnits

end ClassFieldTheory.Brauer
