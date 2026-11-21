/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeAbelianEuler
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalEulerShapiro
public import Nyll.GaloisCohomology.Topology.FiniteStageCoinduction

/-! # Euler characteristic of inflated finite-stage induced coefficients -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory KummerTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace Representation

/-- The original action viewed as a representation on the underlying
integral additive group. -/
def underlyingIntegral {k Q V : Type*} [Ring k] [Monoid Q] [AddCommGroup V]
    [Module k V] (ρ : Representation k Q V) : Representation ℤ Q V where
  toFun g := (ρ g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => congrArg (fun f : Module.End k V => f x) (map_one ρ)
  map_mul' g h := LinearMap.ext fun x =>
    congrArg (fun f : Module.End k V => f x) (map_mul ρ g h)

theorem underlyingIntegral_apply {k Q V : Type*} [Ring k] [Monoid Q] [AddCommGroup V]
    [Module k V] (ρ : Representation k Q V) (g : Q) (v : V) :
    ρ.underlyingIntegral g v = ρ g v := rfl

end Representation

namespace ClassFieldTheory.Brauer
attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (L : FiniteGaloisIntermediateField K (SeparableClosure K))

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)
local notation "Q" => Gal(L/K)
local notation "r" => finiteGaloisRestriction L

/-- The discrete integral coefficient obtained from a finite-stage
representation by the actual absolute restriction homomorphism. -/
abbrev finiteStageIntegralCoefficient {k : Type*} [Ring k] {V : Type u} [AddCommGroup V]
    [Module k V] (ρ : Representation k Q V) : TopRep.{u} ℤ G :=
  TopRep.res (r).toMonoidHom (discreteCoefficientTopRep ℤ Q (Rep.of ρ.underlyingIntegral))

/-- The one-dimensional action of a scalar character on its coefficient field. -/
def scalarCharacterRepresentation {k H : Type u} [Field k] [Group H]
    (χ : H →* k) : Representation k H k :=
  (Algebra.lsmul k k k).toMonoidHom.comp χ

private def stageInducingSubgroup (S : Subgroup Q) : OpenSubgroup Q where
  toSubgroup := S
  isOpen' := isOpen_discrete (S : Set Q)

private abbrev inducingCoefficient (k : Type u) [Field k] (S : Subgroup Q) (χ : S →* k) :
    TopRep.{u} ℤ (stageInducingSubgroup K L S).toSubgroup :=
  discreteCoefficientTopRep ℤ S (Rep.of (scalarCharacterRepresentation χ).underlyingIntegral)

private def finiteStageInducedCoinductionIso
    (k : Type u) [Field k] {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k Q V) (S : Subgroup Q) (χ : S →* k)
    (e : Representation.Equiv (Representation.ind S.subtype (scalarCharacterRepresentation χ)) ρ) :
    finiteStageIntegralCoefficient K L ρ ≅
      TopRep.finiteStageAmbientCoinducedCoefficient (finiteGaloisRestriction L)
        (stageInducingSubgroup K L S) (inducingCoefficient K L k S χ) := by
  classical
  let O := stageInducingSubgroup K L S
  let A := inducingCoefficient K L k S χ
  have hr : Function.Surjective (r) := AlgEquiv.restrictNormalHom_surjective Ω
  let τ : Representation k S k := scalarCharacterRepresentation χ
  let W : Rep.{u} k S := Rep.of τ
  let i : Representation.Equiv (Representation.ind S.subtype τ)
      (Representation.coind S.subtype τ) :=
    Representation.equivOfIso (Rep.indCoindIso W)
  let J := TopRep.res (r).toMonoidHom (TopRep.finiteStageDiscreteCoinducedCoefficient (O) (A))
  let f : V ≃+ J :=
    e.symm.toLinearEquiv.toAddEquiv.trans (i.toLinearEquiv.toAddEquiv.trans
      { toFun := fun x => ⟨x.val, x.property⟩
        invFun := fun x => ⟨x.val, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl })
  have hf (g : G) (x : V) :
      f (ρ ((r) g) x) = (J).ρ g (f x) := by
    apply Subtype.ext
    funext q
    change (i (e.symm (ρ ((r) g) x))).val q = (i (e.symm x)).val (q * (r) g)
    let g₀ : Q := (r) g
    have h₁ := Representation.IntertwiningMap.isIntertwining ρ (Representation.ind S.subtype τ)
      e.symm.toIntertwiningMap g₀ x
    have h₂ := Representation.IntertwiningMap.isIntertwining (Representation.ind S.subtype τ)
      (Representation.coind S.subtype τ) i.toIntertwiningMap g₀ (e.symm x)
    exact congrArg (fun y => y.val q) ((congrArg (fun y => i y) h₁).trans h₂)
  exact (discreteIntegralCoefficientIso f hf).trans (finiteStageCoinductionIso (r) (O) (A) hr)

private theorem continuous_action_restrict
    {J H : Type u} [Group J] [Group H] [TopologicalSpace J] [TopologicalSpace H]
    (f : J →* H) (hf : Continuous f) (A : TopRep.{u} ℤ H)
    (hA : Continuous (fun ha : H × A => A.ρ ha.1 ha.2)) :
    let B := TopRep.res f A
    Continuous (fun ja : J × B => B.ρ ja.1 ja.2) :=
  hA.comp (hf.prodMap (continuous_id : Continuous (id : A → A)))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] in
private theorem finiteStageScalarRestricted_actionContinuous
    (k : Type u) [Field k] (S : Subgroup Q) (χ : S →* k) :
    let O := stageInducingSubgroup K L S
    let U := TopRep.finiteStageOpenSubgroup (finiteGaloisRestriction L) O
    let A := inducingCoefficient K L k S χ
    let B := TopRep.finiteStageRestrictedCoefficient (finiteGaloisRestriction L) O A
    Continuous (fun ga : U.toSubgroup × B => B.ρ ga.1 ga.2) :=
  TopRep.finiteStageSubgroupAction_continuous (finiteGaloisRestriction L)
    (stageInducingSubgroup K L S) (inducingCoefficient K L k S χ)

private theorem finiteStageScalarEuler_overFixedField
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Finite k] [CharP k p]
    (S : Subgroup Q) (χ : S →* k)
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (hfix : E.fixingSubgroup =
      (TopRep.finiteStageOpenSubgroup (finiteGaloisRestriction L)
        (stageInducingSubgroup K L S)).toSubgroup) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (TopRep.finiteStageAmbientCoinducedCoefficient (finiteGaloisRestriction L)
        (stageInducingSubgroup K L S) (inducingCoefficient K L k S χ)) := by
  let O := stageInducingSubgroup K L S
  let U := TopRep.finiteStageOpenSubgroup (finiteGaloisRestriction L) O
  let A := inducingCoefficient K L k S χ
  let B := TopRep.finiteStageRestrictedCoefficient (finiteGaloisRestriction L) O A
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let GE := Gal(SeparableClosure E/E)
  let e := fixedFieldAbsoluteEquiv K (U) E hfix
  let s := finiteStageSubgroupMap (r) (O)
  let D := TopRep.res e.toMonoidHom (B)
  let : Finite B := inferInstanceAs (Finite k)
  let χE : GE →* kˣ := χ.toHomUnits.comp (s.toMonoidHom.comp e.toMonoidHom)
  have hχ : IsLocallyConstant χ.toHomUnits := fun t => isOpen_discrete (χ.toHomUnits ⁻¹' t)
  have χlc : IsLocallyConstant χE := by
    change IsLocallyConstant (χ.toHomUnits ∘ (s ∘ e))
    exact hχ.comp_continuous (s.continuous.comp e.continuous)
  have hB := finiteStageScalarRestricted_actionContinuous K L k S χ
  have hD := continuous_action_restrict e.toMonoidHom e.continuous B hB
  let c : D ≃+ k := AddEquiv.refl k
  have hχE (g : GE) (x : D) : c (D.ρ g x) = (χE g : k) * c x := rfl
  have hEuler := localEulerCoefficient_finiteFieldScalarLine E p k D c χE χlc hχE hD
  exact localEulerCoefficient_openCoinduced K U E hfix B hB hEuler

/-- An induced scalar line at a finite Galois stage satisfies the local Euler
formula for the original inflated module. The inducing subgroup is realized
by its actual fixed field. -/
theorem localEulerCoefficient_finiteStageInducedLine
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Finite k] [CharP k p]
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k Q V)
    (S : Subgroup Q) (χ : S →* k)
    (hρ : Nonempty (Representation.Equiv
      (Representation.ind S.subtype (scalarCharacterRepresentation χ)) ρ)) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K L ρ) := by
  obtain ⟨i⟩ := hρ
  let O := stageInducingSubgroup K L S
  let U := TopRep.finiteStageOpenSubgroup (finiteGaloisRestriction L) O
  obtain ⟨E, hE, hfix, _⟩ := exists_finiteIntermediateField_openSubgroup_equiv_apply U
  let : FiniteDimensional K E := hE
  exact hasLowDegreeEulerCharacteristic_of_iso
    (finiteStageInducedCoinductionIso K L k ρ S χ i).symm
    (finiteStageScalarEuler_overFixedField K L p k S χ E hfix)

end ClassFieldTheory.Brauer
