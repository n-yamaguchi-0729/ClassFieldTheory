/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import Nyll.ClassFieldTheory.Algebra.Brauer.Cohomology

/-! # Base units as absolute Galois invariants -/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousCohomology

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K]

local notation "Ω" => SeparableClosure K
local notation "U" => unitsRep K

/-- The original inclusion of base-field units into the separable closure. -/
def baseUnitsInSeparableClosure : Kˣ →* Ωˣ :=
  Units.map (algebraMap K Ω).toMonoidHom

theorem baseUnitsInSeparableClosure_injective :
    Function.Injective (baseUnitsInSeparableClosure K) := by
  intro a b h
  apply Units.ext
  apply (algebraMap K Ω).injective
  exact congrArg Units.val h

/-- A base-field unit is fixed under the actual separable-closure action. -/
def baseUnitInvariant (b : Kˣ) : (U).invariants :=
  ⟨Additive.ofMul (baseUnitsInSeparableClosure K b), fun σ => by
    apply Additive.toMul.injective
    apply Units.ext
    exact σ.commutes (b : K)⟩

/-- Inclusion of the base-field units as fixed coefficients, written additively. -/
def baseUnitsInvariantHom : Additive Kˣ →+ (U).invariants where
  toFun b := baseUnitInvariant K b.toMul
  map_zero' := Subtype.ext (congrArg Additive.ofMul (map_one (baseUnitsInSeparableClosure K)))
  map_add' b c := Subtype.ext (congrArg Additive.ofMul
    (map_mul (baseUnitsInSeparableClosure K) b.toMul c.toMul))

/-- The invariant units are precisely the units of the base field. -/
def baseUnitsInvariantEquiv : Additive Kˣ ≃+ (U).invariants := by
  apply AddEquiv.ofBijective (baseUnitsInvariantHom K)
  constructor
  · intro a b h
    exact baseUnitsInSeparableClosure_injective K (congrArg (fun z : (U).invariants =>
      (show Additive Ωˣ from z.val).toMul) h)
  · intro z
    let a := (show Additive Ωˣ from z.val).toMul
    have hfix (σ : Gal(Ω/K)) : σ (a : Ω) = a :=
      congrArg (fun b : U => ((show Additive Ωˣ from b).toMul : Ω)) (z.property σ)
    obtain ⟨b, hb⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := Ω) (a : Ω)).mpr hfix
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, map_zero] at hb
      exact a.ne_zero hb.symm
    refine ⟨Additive.ofMul (Units.mk0 b hb0), Subtype.ext ?_⟩
    exact congrArg Additive.ofMul (Units.ext hb)

theorem baseUnitsInvariantEquiv_apply (b : Kˣ) :
    baseUnitsInvariantEquiv K (Additive.ofMul b) = baseUnitInvariant K b := rfl

/-- Evaluation of zero-degree cohomology gives the original base field units. -/
def separableUnitsH0EquivBaseUnits : continuousCohomology 0 U ≃+ Additive Kˣ :=
  (AddEquiv.ofBijective (zeroIso U).hom.hom.toLinearMap.toAddMonoidHom
    (ConcreteCategory.bijective_of_isIso (zeroIso U).hom)).trans (baseUnitsInvariantEquiv K).symm

end ClassFieldTheory.Brauer
