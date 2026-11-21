/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePrimeTransport

/-! # Prime-to-index descent of the local Tate pairings -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ContinuousCohomology LocalFieldTheory TopRep

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+)

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Hcoh" => _root_.continuousCohomology (k := ℤ)

variable (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [DiscreteTopology A]
variable (hn : ((n : ℕ) : K) ≠ 0)

section Prime

open ClassFieldTower.Cohomology

/-- The lifted trivial coefficient has the discrete topology of its original carrier. -/
theorem localTateTrivialCoefficient_discrete (F : Type u) [Field F] (p : ℕ) :
    DiscreteTopology (trivialIntegralZModPLifted p Gal(SeparableClosure F/F)) := by
  change DiscreteTopology (ULift.{u} (ZMod p))
  infer_instance

variable (hline : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ+) [Fact (p : ℕ).Prime] (hpF : ((p : ℕ) : F) ≠ 0)
    {ζ : F}, IsPrimitiveRoot ζ (p : ℕ) →
      let T := trivialIntegralZModPLifted (p : ℕ) Gal(SeparableClosure F/F)
      let : DiscreteTopology T := localTateTrivialCoefficient_discrete F (p : ℕ)
      Function.Bijective (localTatePairingZeroAdjoint F p T hpF) ∧
        Function.Bijective (localTatePairingOneAdjoint F p T hpF) ∧
        Function.Bijective (localTatePairingTwoAdjoint F p T hpF))

include hline

private theorem localTatePairingAdjoints_bijective_prime_of_primitive
    [Fact (n : ℕ).Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ (n : ℕ)) [Finite A]
    (hA : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2)) (hAn : ∀ a : A, (n : ℕ) • a = 0) :
    Function.Bijective (localTatePairingZeroAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n A hn) := by
  let : Module ℤ A := A.hV2
  obtain ⟨U, hU, hρ⟩ := exists_openSubgroup_primeToIndex_pGroup_image ℤ Γabs A hA n
  obtain ⟨E, hE, hfix, _⟩ := KummerTheory.exists_finiteIntermediateField_openSubgroup_equiv_apply U
  let : FiniteDimensional K E := hE
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : IsSepClosure E (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  let : Algebra E (SeparableClosure E) := canonicalSeparableClosureAlgebra E
  let j := IsSepClosure.equiv E (SeparableClosure K) (SeparableClosure E)
  let S := stageOpenFixingSubgroup K E
  have hSU : S = U := OpenSubgroup.toSubgroup_injective hfix
  have hindex : ¬ (n : ℕ) ∣ (S).toSubgroup.index := hSU.symm ▸ hU
  have hρS : IsPGroup (n : ℕ)
      (Representation.asGroupHom (A.ρ.toRepresentation.comp (S).toSubgroup.subtype)).range :=
    hSU.symm ▸ hρ
  let e := embeddedAbsoluteRestrictionEquiv K E j
  let V := embeddedTateCoefficients K A E j
  let Γabs' := Gal(SeparableClosure E/E)
  let : Finite V := inferInstanceAs (Finite A)
  let : DiscreteTopology V := inferInstanceAs (DiscreteTopology A)
  let : Module ℤ V := (V).hV2
  have hV : Continuous (fun g'a : Γabs' × V => (V).ρ g'a.1 g'a.2) :=
    hA.comp ((continuous_subtype_val.comp (e).continuous).prodMap continuous_id)
  have hρV : IsPGroup (n : ℕ) (V).ρ.toRepresentation.asGroupHom.range := by
    let α := (V).ρ.toRepresentation.asGroupHom
    let β := Representation.asGroupHom (A.ρ.toRepresentation.comp (S).toSubgroup.subtype)
    have hle : α.range ≤ β.range := by
      intro x hx
      obtain ⟨σ, hσ⟩ := hx
      have he : β (e σ) = α σ := rfl
      exact ⟨e σ, he.trans hσ⟩
    exact hρS.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hnE : ((n : ℕ) : E) ≠ 0 := by
    have h := (algebraMap K E).injective.ne hn
    simpa only [map_natCast, map_zero] using h
  have hζE : IsPrimitiveRoot (algebraMap K E ζ) (n : ℕ) :=
    hζ.map_of_injective (f := algebraMap K E) (algebraMap K E).injective
  have h₃ (X : TopRep.{u} ℤ Γabs') [Finite X] [DiscreteTopology X]
      (hX : Continuous (fun gx : Γabs' × X => X.ρ gx.1 gx.2)) (_ : ∀ x : X, (n : ℕ) • x = 0) :
      ∀ x : Hcoh 3 X, x = 0 :=
    cohomology_eq_zero_of_continuousModuleComplex_isZero Γabs' X 3
      (finiteLocalIntegralH3_isZero E X hX)
  obtain ⟨hzero, hone, htwo⟩ :=
    localTatePairingAdjoints_bijective_of_pGroup_image E n hnE n dvd_rfl h₃
    (hline E n hnE hζE) V hV hAn hρV
  obtain ⟨hzero', hone', htwo'⟩ :=
    openLocalTatePairingAdjoints_bijective_of_embedded K n A hn E j hnE hzero hone htwo
  exact localTatePairingAdjoints_bijective_of_primeToIndex_openSubgroup K n A S hn
    hindex hAn hzero' hone' htwo'

/-- Local pairings for prime-annihilated coefficients reduce to the trivial
prime line over fields containing a primitive root. The two transfers use
the cyclotomic stage and the Sylow preimage of the original coefficient action. -/
theorem localTatePairingAdjoints_bijective_prime
    [Fact (n : ℕ).Prime] [Finite A]
    (hA : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2)) (hAn : ∀ a : A, (n : ℕ) • a = 0) :
    Function.Bijective (localTatePairingZeroAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n A hn) := by
  obtain ⟨E, hE, ζ, hζ, hindex⟩ := exists_primitiveRoot_finite_stage_primeToIndex K n hn
  let : FiniteDimensional K E := hE
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : IsSepClosure E (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  let : Algebra E (SeparableClosure E) := canonicalSeparableClosureAlgebra E
  let j := IsSepClosure.equiv E (SeparableClosure K) (SeparableClosure E)
  let S := stageOpenFixingSubgroup K E
  let e := embeddedAbsoluteRestrictionEquiv K E j
  let V := embeddedTateCoefficients K A E j
  let Γabs' := Gal(SeparableClosure E/E)
  let : Finite V := inferInstanceAs (Finite A)
  let : DiscreteTopology V := inferInstanceAs (DiscreteTopology A)
  have hV : Continuous (fun g'a : Γabs' × V => (V).ρ g'a.1 g'a.2) :=
    hA.comp ((continuous_subtype_val.comp (e).continuous).prodMap continuous_id)
  have hnE : ((n : ℕ) : E) ≠ 0 := by
    have h := (algebraMap K E).injective.ne hn
    simpa only [map_natCast, map_zero] using h
  obtain ⟨hzero, hone, htwo⟩ :=
    localTatePairingAdjoints_bijective_prime_of_primitive E n V hnE hline hζ hV hAn
  obtain ⟨hzero', hone', htwo'⟩ :=
    openLocalTatePairingAdjoints_bijective_of_embedded K n A hn E j hnE hzero hone htwo
  exact localTatePairingAdjoints_bijective_of_primeToIndex_openSubgroup K n A S hn
    hindex hAn hzero' hone' htwo'

/-- Finite local Tate duality reduces to its primitive-root trivial prime
case using the original cup products, trace, maps and exact sequences. -/
theorem localTatePairingAdjoints_bijective_of_trivialPrimeLine [Finite A]
    (hA : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2)) (hAn : ∀ a : A, (n : ℕ) • a = 0) :
    Function.Bijective (localTatePairingZeroAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n A hn) := by
  apply localTatePairingAdjoints_bijective_of_prime_coefficients K n hn ?_ ?_ A hA hAn
  · intro X _ _ hX _
    exact cohomology_eq_zero_of_continuousModuleComplex_isZero Γabs X 3
      (finiteLocalIntegralH3_isZero K X hX)
  · intro p hp hdvd X _ _ hX hpX
    let m : ℕ+ := ⟨p, hp.pos⟩
    let : Fact (m : ℕ).Prime := ⟨hp⟩
    have hm : ((m : ℕ) : K) ≠ 0 := by
      intro h
      obtain ⟨q, hq⟩ := hdvd
      have hcast : (n : ℕ) = (m : ℕ) * q := hq
      exact hn ((congrArg (Nat.cast : ℕ → K) hcast).trans (by rw [Nat.cast_mul, h, zero_mul]))
    exact localTatePairingAdjoints_bijective_of_dvd K m n hdvd hm hn X hpX
      (localTatePairingAdjoints_bijective_prime K m X hm hline hX hpX)

end Prime

end ClassFieldTheory.Brauer
