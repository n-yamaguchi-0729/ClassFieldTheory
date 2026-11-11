/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChangeCoherence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReconstruction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.NativeRayArtinTransfer
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate

/-!
# Original transfer forces reconstructed multiplication to respect fixed fields

At two actual finite Galois fixed fields, the native ray transfers already
satisfy original reciprocity. If the original ray quotient comparisons
commute with these group transfers, their reconstructed restricted-product
maps have the same Artin image.

The actual place-restriction square and ramification indices give equal
orders and support. Another original boundary supplies a genuine anchor,
so separation before reciprocity gives the actual restricted-product
square. Restricting to the original principal kernels then proves that
the recovered function-unit maps commute with literal field inclusion.

No commutation of reconstructed local maps, restricted families, or
function units is assumed.
-/

noncomputable section

open AlgebraicCurve ClassFormation LocalClassFieldTheory

namespace FunctionField.RayClass

-- Reuse the native closure owners already used by the transfer construction.
attribute [local instance]
  nativeRayFixedFieldSeparableClosureAlgebra nativeRayFixedFieldSeparableClosureSMul

private theorem nativeReciprocitySquare
    {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    [TopologicalSpace C] [TopologicalSpace D]
    {f : B →* D} {g : A →* B} {h : C →ₜ* D} {s : A →* C}
    (law : ∀ a, f (g a) = h (s a)) : f.comp g = h.toMonoidHom.comp s :=
  MonoidHom.ext law

section AbstractFiniteBaseChange

variable {k₁ K₁ L₁ k₂ K₂ L₂ : Type*}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field L₁] [Algebra k₁ L₁] [Algebra K₁ L₁] [IsScalarTower k₁ K₁ L₁]
    [FiniteDimensional K₁ L₁]
    [Algebra (RatFunc k₁) L₁] [IsScalarTower k₁ (RatFunc k₁) L₁]
    [FunctionField k₁ L₁] [HasPrincipalDivisors k₁ L₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]
    [Field L₂] [Algebra k₂ L₂] [Algebra K₂ L₂] [IsScalarTower k₂ K₂ L₂]
    [FiniteDimensional K₂ L₂]
    [Algebra (RatFunc k₂) L₂] [IsScalarTower k₂ (RatFunc k₂) L₂]
    [FunctionField k₂ L₂] [HasPrincipalDivisors k₂ L₂]
    (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
    (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (eF : Place k₁ L₁ ≃ Place k₂ L₂)

local notation "M₁" => rayModulusBaseChange L₁ m₁
local notation "M₂" => rayModulusBaseChange L₂ m₂

variable
    (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
      (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
    (Γ : (localAbsoluteAbelianProfinite L₁ ⧸ artinRaySubgroup (rayModulusBaseChange L₁ m₁)) ≃*
      (localAbsoluteAbelianProfinite L₂ ⧸ artinRaySubgroup (rayModulusBaseChange L₂ m₂)))
    (hclosure : ∀ v g,
      g ∈ (localRayAbsoluteArtin m₁ v).range.topologicalClosure ↔
        γ g ∈ (localRayAbsoluteArtin m₂ (e v)).range.topologicalClosure)
    (hdegree : ∀ g, rayAbelianDegree m₂ (γ g) = rayAbelianDegree m₁ g)
    (hclosureF : ∀ w g,
      g ∈ (localRayAbsoluteArtin (rayModulusBaseChange L₁ m₁) w).range.topologicalClosure ↔
        Γ g ∈ (localRayAbsoluteArtin (rayModulusBaseChange L₂ m₂) (eF w)).range.topologicalClosure)
    (hdegreeF : ∀ g, rayAbelianDegree (rayModulusBaseChange L₂ m₂) (Γ g) =
      rayAbelianDegree (rayModulusBaseChange L₁ m₁) g)
    (hboundary₁ : ∀ v : Place k₁ K₁, ∃ z : Place k₁ K₁, z ≠ v ∧ m₁ z ≠ 0)
    (hboundary₂ : ∀ v : Place k₂ K₂, ∃ z : Place k₂ K₂, z ≠ v ∧ m₂ z ≠ 0)

local notation "hbF₁" => rayModulusBaseChange_other_boundary (L := L₁) m₁ hboundary₁
local notation "hbF₂" => rayModulusBaseChange_other_boundary (L := L₂) m₂ hboundary₂
local notation "ρ" => reconstructedRestrictedRayEquiv m₁ m₂ e γ
  hclosure hdegree hboundary₁ hboundary₂
local notation "ρF" => reconstructedRestrictedRayEquiv M₁ M₂ eF Γ
  hclosureF hdegreeF hbF₁ hbF₂
local notation "b₁" => restrictedRayBaseChange (L := L₁) m₁ hm₁
local notation "b₂" => restrictedRayBaseChange (L := L₂) m₂ hm₂

variable
    (τ₁ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) →ₜ*
      (localAbsoluteAbelianProfinite L₁ ⧸ artinRaySubgroup (rayModulusBaseChange L₁ m₁)))
    (τ₂ : (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂) →ₜ*
      (localAbsoluteAbelianProfinite L₂ ⧸ artinRaySubgroup (rayModulusBaseChange L₂ m₂)))
    (hplaces : ∀ w : Place k₁ L₁, (eF w).restrict K₂ = e (w.restrict K₁))
    (hindex : ∀ w : Place k₁ L₁,
      w.ramificationIndex K₁ = (eF w).ramificationIndex K₂)
    (htransfer : ∀ g, Γ (τ₁ g) = τ₂ (γ g))
    (hlower :
      (restrictedProductAbsoluteArtin (rayModulusBaseChange L₁ m₁)).comp
        (restrictedRayBaseChange (L := L₁) m₁ hm₁) =
      τ₁.toMonoidHom.comp (restrictedProductAbsoluteArtin m₁))
    (hupper :
      (restrictedProductAbsoluteArtin (rayModulusBaseChange L₂ m₂)).comp
        (restrictedRayBaseChange (L := L₂) m₂ hm₂) =
      τ₂.toMonoidHom.comp (restrictedProductAbsoluteArtin m₂))

include hplaces hindex htransfer hlower hupper

-- Carry out the separation, principal-kernel restriction, and adjoining zero
-- over abstract finite extensions; fixed-field presentations are supplied below.
private theorem reconstructedRestrictedRayEquiv_baseChange_core :
    (ρF).toMonoidHom.comp b₁ = (b₂).comp (ρ).toMonoidHom := by
  let φ := fun v => localRayEquivOfClosure m₁ v m₂ (e v)
    γ (hclosure v) hdegree (hboundary₁ v) (hboundary₂ (e v))
  let ψ := fun w => localRayEquivOfClosure M₁ w M₂ (eF w)
    Γ (hclosureF w) hdegreeF (hbF₁ w) (hbF₂ (eF w))
  apply restrictedRayEquiv_baseChange_of_artin_square m₁ m₂ hm₁ hm₂ e eF hplaces φ ψ
    (fun v a => localRayFactorOrder_map m₁ v m₂ (e v) γ
      (hclosure v) hdegree (hboundary₁ v) (hboundary₂ (e v)) a)
    (fun w a => localRayFactorOrder_map M₁ w M₂ (eF w) Γ
      (hclosureF w) hdegreeF (hbF₁ w) (hbF₂ (eF w)) a)
    hindex hboundary₂
  apply MonoidHom.ext
  intro a
  change restrictedProductAbsoluteArtin M₂ (ρF (b₁ a)) =
    restrictedProductAbsoluteArtin M₂ (b₂ (ρ a))
  calc
    restrictedProductAbsoluteArtin M₂ (ρF (b₁ a)) =
        Γ (restrictedProductAbsoluteArtin M₁ (b₁ a)) :=
      reconstructedRestrictedRayEquiv_artin M₁ M₂ eF Γ
        hclosureF hdegreeF hbF₁ hbF₂ (b₁ a)
    _ = Γ (τ₁ (restrictedProductAbsoluteArtin m₁ a)) :=
      congrArg Γ
        (DFunLike.congr_fun hlower a)
    _ = τ₂ (γ (restrictedProductAbsoluteArtin m₁ a)) :=
      htransfer (restrictedProductAbsoluteArtin m₁ a)
    _ = τ₂ (restrictedProductAbsoluteArtin m₂ (ρ a)) :=
      congrArg τ₂
        (reconstructedRestrictedRayEquiv_artin m₁ m₂ e γ
          hclosure hdegree hboundary₁ hboundary₂ a).symm
    _ = restrictedProductAbsoluteArtin M₂ (b₂ (ρ a)) :=
      (DFunLike.congr_fun hupper (ρ a)).symm

variable (hmzero₁ : m₁ ≠ 0) (hmzero₂ : m₂ ≠ 0)

local notation "η" => reconstructedRayFunctionUnits m₁ m₂ e γ
  hclosure hdegree hboundary₁ hboundary₂ hmzero₁ hmzero₂
local notation "ηF" => reconstructedRayFunctionUnits M₁ M₂ eF Γ
  hclosureF hdegreeF hbF₁ hbF₂
  (rayModulusBaseChange_ne_zero m₁ hmzero₁) (rayModulusBaseChange_ne_zero m₂ hmzero₂)

private theorem reconstructedRayFunctionUnits_baseChange_core (x : K₁ˣ) :
    ηF (Units.map (algebraMap K₁ L₁) x) = Units.map (algebraMap K₂ L₂) (η x) := by
  have hcoherence := reconstructedRestrictedRayEquiv_baseChange_core
    (m₁ := m₁) (m₂ := m₂) (hm₁ := hm₁) (hm₂ := hm₂) (e := e) (eF := eF)
    (γ := γ) (Γ := Γ) (hclosure := hclosure) (hdegree := hdegree)
    (hclosureF := hclosureF) (hdegreeF := hdegreeF)
    (hboundary₁ := hboundary₁) (hboundary₂ := hboundary₂)
    (τ₁ := τ₁) (τ₂ := τ₂) (hplaces := hplaces) (hindex := hindex)
    (htransfer := htransfer) (hlower := hlower) (hupper := hupper)
  have hprincipalLower := reconstructedRayFunctionUnits_principal m₁ m₂ e γ
    hclosure hdegree hboundary₁ hboundary₂ hmzero₁ hmzero₂ x
  have hprincipalUpper := reconstructedRayFunctionUnits_principal M₁ M₂ eF Γ
    hclosureF hdegreeF hbF₁ hbF₂
    (rayModulusBaseChange_ne_zero m₁ hmzero₁) (rayModulusBaseChange_ne_zero m₂ hmzero₂)
    (Units.map (algebraMap K₁ L₁) x)
  simp only [principalRestrictedArtinKernelEquiv_coe] at hprincipalLower hprincipalUpper
  apply (principalRestrictedArtinKernelEquiv M₂
    (rayModulusBaseChange_ne_zero m₂ hmzero₂)).injective
  apply Subtype.ext
  simp only [principalRestrictedArtinKernelEquiv_coe]
  calc
    principalToRayRestrictedProduct M₂ (ηF (Units.map (algebraMap K₁ L₁) x)) =
        ρF (principalToRayRestrictedProduct M₁ (Units.map (algebraMap K₁ L₁) x)) :=
      hprincipalUpper
    _ = ρF (b₁ (principalToRayRestrictedProduct m₁ x)) :=
      congrArg ρF (restrictedRayBaseChange_principal m₁ hm₁ x).symm
    _ = b₂ (ρ (principalToRayRestrictedProduct m₁ x)) :=
      DFunLike.congr_fun hcoherence (principalToRayRestrictedProduct m₁ x)
    _ = b₂ (principalToRayRestrictedProduct m₂ (η x)) :=
      congrArg b₂ hprincipalLower.symm
    _ = principalToRayRestrictedProduct M₂ (Units.map (algebraMap K₂ L₂) (η x)) :=
      restrictedRayBaseChange_principal m₂ hm₂ (η x)

local notation "η₀" => reconstructedRayFunction m₁ m₂ e γ
  hclosure hdegree hboundary₁ hboundary₂ hmzero₁ hmzero₂
local notation "ηF₀" => reconstructedRayFunction M₁ M₂ eF Γ
  hclosureF hdegreeF hbF₁ hbF₂
  (rayModulusBaseChange_ne_zero m₁ hmzero₁) (rayModulusBaseChange_ne_zero m₂ hmzero₂)

private theorem reconstructedRayFunction_baseChange_core (x : K₁) :
    ηF₀ (algebraMap K₁ L₁ x) = algebraMap K₂ L₂ (η₀ x) := by
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp only [map_zero]
  · change ηF₀ ((Units.map (algebraMap K₁ L₁) u : L₁ˣ) : L₁) =
      algebraMap K₂ L₂ (η₀ (u : K₁))
    rw [reconstructedRayFunction_apply_units, reconstructedRayFunction_apply_units]
    exact congrArg (fun y : L₂ˣ => (y : L₂))
      (reconstructedRayFunctionUnits_baseChange_core
        (m₁ := m₁) (m₂ := m₂) (hm₁ := hm₁) (hm₂ := hm₂) (e := e) (eF := eF)
        (γ := γ) (Γ := Γ) (hclosure := hclosure) (hdegree := hdegree)
        (hclosureF := hclosureF) (hdegreeF := hdegreeF)
        (hboundary₁ := hboundary₁) (hboundary₂ := hboundary₂)
        (τ₁ := τ₁) (τ₂ := τ₂) (hplaces := hplaces) (hindex := hindex)
        (htransfer := htransfer) (hlower := hlower) (hupper := hupper)
        (hmzero₁ := hmzero₁) (hmzero₂ := hmzero₂) u)

end AbstractFiniteBaseChange

/-- Covariance of the original native group transfers forces the
reconstructed ray maps to commute with literal finite-field base change.
Both reciprocity squares are the proved native transfer formulas. -/
theorem reconstructedRestrictedRayEquiv_fixedField_baseChange
    {k₁ K₁ k₂ K₂ : Type*}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]
    (H₁ : FiniteAbstractField Gal(SeparableClosure K₁/K₁))
    (H₂ : FiniteAbstractField Gal(SeparableClosure K₂/K₂))
    [H₁.field.toSubgroup.Normal] [H₂.field.toSubgroup.Normal] :
    let F₁ := abstractFixedField K₁ (SeparableClosure K₁) H₁.field
    let F₂ := abstractFixedField K₂ (SeparableClosure K₂) H₂.field
    let : Algebra k₁ (SeparableClosure K₁) :=
      ((algebraMap K₁ (SeparableClosure K₁)).comp (algebraMap k₁ K₁)).toAlgebra
    let : Algebra (RatFunc k₁) (SeparableClosure K₁) :=
      ((algebraMap K₁ (SeparableClosure K₁)).comp (algebraMap (RatFunc k₁) K₁)).toAlgebra
    let : IsScalarTower k₁ K₁ (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower (RatFunc k₁) K₁ (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower k₁ (RatFunc k₁) (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K₁ (SeparableClosure K₁))
        (IsScalarTower.algebraMap_apply k₁ (RatFunc k₁) K₁ x))
    let : FiniteDimensional K₁ F₁ :=
      abstractFixedField_finiteDimensional K₁ (SeparableClosure K₁) H₁.field H₁.finite
    let : FunctionField k₁ F₁ :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k₁) (K := K₁) (Ω := SeparableClosure K₁) F₁
    let : HasPrincipalDivisors k₁ F₁ :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k₁ K₁ F₁).toHasPrincipalDivisors
    let : Algebra k₂ (SeparableClosure K₂) :=
      ((algebraMap K₂ (SeparableClosure K₂)).comp (algebraMap k₂ K₂)).toAlgebra
    let : Algebra (RatFunc k₂) (SeparableClosure K₂) :=
      ((algebraMap K₂ (SeparableClosure K₂)).comp (algebraMap (RatFunc k₂) K₂)).toAlgebra
    let : IsScalarTower k₂ K₂ (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower (RatFunc k₂) K₂ (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower k₂ (RatFunc k₂) (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K₂ (SeparableClosure K₂))
        (IsScalarTower.algebraMap_apply k₂ (RatFunc k₂) K₂ x))
    let : FiniteDimensional K₂ F₂ :=
      abstractFixedField_finiteDimensional K₂ (SeparableClosure K₂) H₂.field H₂.finite
    let : FunctionField k₂ F₂ :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k₂) (K := K₂) (Ω := SeparableClosure K₂) F₂
    let : HasPrincipalDivisors k₂ F₂ :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k₂ K₂ F₂).toHasPrincipalDivisors
    ∀ (ε₁ : SeparableClosure F₁ ≃ₐ[F₁] SeparableClosure K₁)
      (ε₂ : SeparableClosure F₂ ≃ₐ[F₂] SeparableClosure K₂)
      (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
      (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
      (e : Place k₁ K₁ ≃ Place k₂ K₂)
      (eF : Place k₁ F₁ ≃ Place k₂ F₂),
    let M₁ := rayModulusBaseChange F₁ m₁
    let M₂ := rayModulusBaseChange F₂ m₂
    ∀ (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
        (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
      (Γ : (localAbsoluteAbelianProfinite F₁ ⧸ artinRaySubgroup M₁) ≃*
        (localAbsoluteAbelianProfinite F₂ ⧸ artinRaySubgroup M₂))
      (hclosure : ∀ v g,
        g ∈ (localRayAbsoluteArtin m₁ v).range.topologicalClosure ↔
          γ g ∈ (localRayAbsoluteArtin m₂ (e v)).range.topologicalClosure)
      (hdegree : ∀ g, rayAbelianDegree m₂ (γ g) = rayAbelianDegree m₁ g)
      (hclosureF : ∀ w g,
        g ∈ (localRayAbsoluteArtin M₁ w).range.topologicalClosure ↔
          Γ g ∈ (localRayAbsoluteArtin M₂ (eF w)).range.topologicalClosure)
      (hdegreeF : ∀ g, rayAbelianDegree M₂ (Γ g) = rayAbelianDegree M₁ g)
      (hboundary₁ : ∀ v : Place k₁ K₁, ∃ z : Place k₁ K₁, z ≠ v ∧ m₁ z ≠ 0)
      (hboundary₂ : ∀ v : Place k₂ K₂, ∃ z : Place k₂ K₂, z ≠ v ∧ m₂ z ≠ 0),
    let hbF₁ := rayModulusBaseChange_other_boundary (L := F₁) m₁ hboundary₁
    let hbF₂ := rayModulusBaseChange_other_boundary (L := F₂) m₂ hboundary₂
    let τ₁ := nativeRayTransferOfFixedField k₁ K₁ H₁ ε₁ m₁ hm₁
    let τ₂ := nativeRayTransferOfFixedField k₂ K₂ H₂ ε₂ m₂ hm₂
    ∀ (_ : ∀ w : Place k₁ F₁, (eF w).restrict K₂ = e (w.restrict K₁))
      (_ : ∀ w : Place k₁ F₁,
        w.ramificationIndex K₁ = (eF w).ramificationIndex K₂)
      (_ : ∀ g, Γ (τ₁ g) = τ₂ (γ g)),
    let ρ := reconstructedRestrictedRayEquiv m₁ m₂ e γ
      hclosure hdegree hboundary₁ hboundary₂
    let ρF := reconstructedRestrictedRayEquiv M₁ M₂ eF Γ
      hclosureF hdegreeF hbF₁ hbF₂
    let b₁ := restrictedRayBaseChange (L := F₁) m₁ hm₁
    let b₂ := restrictedRayBaseChange (L := F₂) m₂ hm₂
    (ρF).toMonoidHom.comp b₁ = (b₂).comp (ρ).toMonoidHom := by
  intro F₁ F₂ ak₁Ω aR₁Ω hk₁K₁Ω hR₁K₁Ω hk₁R₁Ω hK₁F₁ hF₁field hF₁principal
    ak₂Ω aR₂Ω hk₂K₂Ω hR₂K₂Ω hk₂R₂Ω hK₂F₂ hF₂field hF₂principal
    ε₁ ε₂ m₁ m₂ hm₁ hm₂ e eF M₁ M₂ γ Γ hclosure hdegree hclosureF hdegreeF
    hboundary₁ hboundary₂ hbF₁ hbF₂ τ₁ τ₂ hplaces hindex htransfer ρ ρF b₁ b₂
  have hlowerNative :=
    restrictedProductAbsoluteArtin_baseChange_nativeTransfer k₁ K₁ H₁ ε₁ m₁ hm₁
  have hlower := nativeReciprocitySquare
    (h := nativeRayTransferOfFixedField k₁ K₁ H₁ ε₁ m₁ hm₁)
    (s := restrictedProductAbsoluteArtin m₁) hlowerNative
  have hupperNative :=
    restrictedProductAbsoluteArtin_baseChange_nativeTransfer k₂ K₂ H₂ ε₂ m₂ hm₂
  have hupper := nativeReciprocitySquare
    (h := nativeRayTransferOfFixedField k₂ K₂ H₂ ε₂ m₂ hm₂)
    (s := restrictedProductAbsoluteArtin m₂) hupperNative
  exact reconstructedRestrictedRayEquiv_baseChange_core (L₁ := F₁) (L₂ := F₂)
    (m₁ := m₁) (m₂ := m₂) (hm₁ := hm₁) (hm₂ := hm₂) (e := e) (eF := eF)
    (γ := γ) (Γ := Γ) (hclosure := hclosure) (hdegree := hdegree)
    (hclosureF := hclosureF) (hdegreeF := hdegreeF)
    (hboundary₁ := hboundary₁) (hboundary₂ := hboundary₂)
    (τ₁ := τ₁) (τ₂ := τ₂) (hplaces := hplaces) (hindex := hindex)
    (htransfer := htransfer)
    (hlower := hlower) (hupper := hupper)

/-- On the actual principal kernels, original transfer covariance yields
commutation of the reconstructed multiplication with the literal inclusions
of the two finite fixed fields. -/
theorem reconstructedRayFunctionUnits_fixedField_baseChange
    {k₁ K₁ k₂ K₂ : Type*}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]
    (H₁ : FiniteAbstractField Gal(SeparableClosure K₁/K₁))
    (H₂ : FiniteAbstractField Gal(SeparableClosure K₂/K₂))
    [H₁.field.toSubgroup.Normal] [H₂.field.toSubgroup.Normal] :
    let F₁ := abstractFixedField K₁ (SeparableClosure K₁) H₁.field
    let F₂ := abstractFixedField K₂ (SeparableClosure K₂) H₂.field
    let : Algebra k₁ (SeparableClosure K₁) :=
      ((algebraMap K₁ (SeparableClosure K₁)).comp (algebraMap k₁ K₁)).toAlgebra
    let : Algebra (RatFunc k₁) (SeparableClosure K₁) :=
      ((algebraMap K₁ (SeparableClosure K₁)).comp (algebraMap (RatFunc k₁) K₁)).toAlgebra
    let : IsScalarTower k₁ K₁ (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower (RatFunc k₁) K₁ (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower k₁ (RatFunc k₁) (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K₁ (SeparableClosure K₁))
        (IsScalarTower.algebraMap_apply k₁ (RatFunc k₁) K₁ x))
    let : FiniteDimensional K₁ F₁ :=
      abstractFixedField_finiteDimensional K₁ (SeparableClosure K₁) H₁.field H₁.finite
    let : FunctionField k₁ F₁ :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k₁) (K := K₁) (Ω := SeparableClosure K₁) F₁
    let : HasPrincipalDivisors k₁ F₁ :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k₁ K₁ F₁).toHasPrincipalDivisors
    let : Algebra k₂ (SeparableClosure K₂) :=
      ((algebraMap K₂ (SeparableClosure K₂)).comp (algebraMap k₂ K₂)).toAlgebra
    let : Algebra (RatFunc k₂) (SeparableClosure K₂) :=
      ((algebraMap K₂ (SeparableClosure K₂)).comp (algebraMap (RatFunc k₂) K₂)).toAlgebra
    let : IsScalarTower k₂ K₂ (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower (RatFunc k₂) K₂ (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower k₂ (RatFunc k₂) (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K₂ (SeparableClosure K₂))
        (IsScalarTower.algebraMap_apply k₂ (RatFunc k₂) K₂ x))
    let : FiniteDimensional K₂ F₂ :=
      abstractFixedField_finiteDimensional K₂ (SeparableClosure K₂) H₂.field H₂.finite
    let : FunctionField k₂ F₂ :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k₂) (K := K₂) (Ω := SeparableClosure K₂) F₂
    let : HasPrincipalDivisors k₂ F₂ :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k₂ K₂ F₂).toHasPrincipalDivisors
    ∀ (ε₁ : SeparableClosure F₁ ≃ₐ[F₁] SeparableClosure K₁)
      (ε₂ : SeparableClosure F₂ ≃ₐ[F₂] SeparableClosure K₂)
      (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
      (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
      (e : Place k₁ K₁ ≃ Place k₂ K₂)
      (eF : Place k₁ F₁ ≃ Place k₂ F₂),
    let M₁ := rayModulusBaseChange F₁ m₁
    let M₂ := rayModulusBaseChange F₂ m₂
    ∀ (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
        (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
      (Γ : (localAbsoluteAbelianProfinite F₁ ⧸ artinRaySubgroup M₁) ≃*
        (localAbsoluteAbelianProfinite F₂ ⧸ artinRaySubgroup M₂))
      (hclosure : ∀ v g,
        g ∈ (localRayAbsoluteArtin m₁ v).range.topologicalClosure ↔
          γ g ∈ (localRayAbsoluteArtin m₂ (e v)).range.topologicalClosure)
      (hdegree : ∀ g, rayAbelianDegree m₂ (γ g) = rayAbelianDegree m₁ g)
      (hclosureF : ∀ w g,
        g ∈ (localRayAbsoluteArtin M₁ w).range.topologicalClosure ↔
          Γ g ∈ (localRayAbsoluteArtin M₂ (eF w)).range.topologicalClosure)
      (hdegreeF : ∀ g, rayAbelianDegree M₂ (Γ g) = rayAbelianDegree M₁ g)
      (hboundary₁ : ∀ v : Place k₁ K₁, ∃ z : Place k₁ K₁, z ≠ v ∧ m₁ z ≠ 0)
      (hboundary₂ : ∀ v : Place k₂ K₂, ∃ z : Place k₂ K₂, z ≠ v ∧ m₂ z ≠ 0),
    let hbF₁ := rayModulusBaseChange_other_boundary (L := F₁) m₁ hboundary₁
    let hbF₂ := rayModulusBaseChange_other_boundary (L := F₂) m₂ hboundary₂
    let τ₁ := nativeRayTransferOfFixedField k₁ K₁ H₁ ε₁ m₁ hm₁
    let τ₂ := nativeRayTransferOfFixedField k₂ K₂ H₂ ε₂ m₂ hm₂
    ∀ (_ : ∀ w : Place k₁ F₁, (eF w).restrict K₂ = e (w.restrict K₁))
      (_ : ∀ w : Place k₁ F₁,
        w.ramificationIndex K₁ = (eF w).ramificationIndex K₂)
      (_ : ∀ g, Γ (τ₁ g) = τ₂ (γ g)),
    ∀ (hmzero₁ : m₁ ≠ 0) (hmzero₂ : m₂ ≠ 0),
    let η := reconstructedRayFunctionUnits m₁ m₂ e γ
      hclosure hdegree hboundary₁ hboundary₂ hmzero₁ hmzero₂
    let ηF := reconstructedRayFunctionUnits M₁ M₂ eF Γ
      hclosureF hdegreeF hbF₁ hbF₂
      (rayModulusBaseChange_ne_zero m₁ hmzero₁) (rayModulusBaseChange_ne_zero m₂ hmzero₂)
    ∀ x : K₁ˣ,
    ηF (Units.map (algebraMap K₁ F₁) x) =
      Units.map (algebraMap K₂ F₂) (η x) := by
  intro F₁ F₂ ak₁Ω aR₁Ω hk₁K₁Ω hR₁K₁Ω hk₁R₁Ω hK₁F₁ hF₁field hF₁principal
    ak₂Ω aR₂Ω hk₂K₂Ω hR₂K₂Ω hk₂R₂Ω hK₂F₂ hF₂field hF₂principal
    ε₁ ε₂ m₁ m₂ hm₁ hm₂ e eF M₁ M₂ γ Γ hclosure hdegree hclosureF hdegreeF
    hboundary₁ hboundary₂ hbF₁ hbF₂ τ₁ τ₂ hplaces hindex htransfer hmzero₁ hmzero₂ η ηF x
  have hlowerNative :=
    restrictedProductAbsoluteArtin_baseChange_nativeTransfer k₁ K₁ H₁ ε₁ m₁ hm₁
  have hlower := nativeReciprocitySquare
    (h := nativeRayTransferOfFixedField k₁ K₁ H₁ ε₁ m₁ hm₁)
    (s := restrictedProductAbsoluteArtin m₁) hlowerNative
  have hupperNative :=
    restrictedProductAbsoluteArtin_baseChange_nativeTransfer k₂ K₂ H₂ ε₂ m₂ hm₂
  have hupper := nativeReciprocitySquare
    (h := nativeRayTransferOfFixedField k₂ K₂ H₂ ε₂ m₂ hm₂)
    (s := restrictedProductAbsoluteArtin m₂) hupperNative
  exact reconstructedRayFunctionUnits_baseChange_core (L₁ := F₁) (L₂ := F₂)
    (m₁ := m₁) (m₂ := m₂) (hm₁ := hm₁) (hm₂ := hm₂) (e := e) (eF := eF)
    (γ := γ) (Γ := Γ) (hclosure := hclosure) (hdegree := hdegree)
    (hclosureF := hclosureF) (hdegreeF := hdegreeF)
    (hboundary₁ := hboundary₁) (hboundary₂ := hboundary₂)
    (τ₁ := τ₁) (τ₂ := τ₂) (hplaces := hplaces) (hindex := hindex)
    (htransfer := htransfer)
    (hlower := hlower) (hupper := hupper)
    (hmzero₁ := hmzero₁) (hmzero₂ := hmzero₂) x

/-- Adjoining zero preserves the same actual fixed-field inclusion square;
the resulting map is already the reconstructed multiplication on functions. -/
theorem reconstructedRayFunction_fixedField_baseChange
    {k₁ K₁ k₂ K₂ : Type*}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]
    (H₁ : FiniteAbstractField Gal(SeparableClosure K₁/K₁))
    (H₂ : FiniteAbstractField Gal(SeparableClosure K₂/K₂))
    [H₁.field.toSubgroup.Normal] [H₂.field.toSubgroup.Normal] :
    let F₁ := abstractFixedField K₁ (SeparableClosure K₁) H₁.field
    let F₂ := abstractFixedField K₂ (SeparableClosure K₂) H₂.field
    let : Algebra k₁ (SeparableClosure K₁) :=
      ((algebraMap K₁ (SeparableClosure K₁)).comp (algebraMap k₁ K₁)).toAlgebra
    let : Algebra (RatFunc k₁) (SeparableClosure K₁) :=
      ((algebraMap K₁ (SeparableClosure K₁)).comp (algebraMap (RatFunc k₁) K₁)).toAlgebra
    let : IsScalarTower k₁ K₁ (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower (RatFunc k₁) K₁ (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower k₁ (RatFunc k₁) (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K₁ (SeparableClosure K₁))
        (IsScalarTower.algebraMap_apply k₁ (RatFunc k₁) K₁ x))
    let : FiniteDimensional K₁ F₁ :=
      abstractFixedField_finiteDimensional K₁ (SeparableClosure K₁) H₁.field H₁.finite
    let : FunctionField k₁ F₁ :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k₁) (K := K₁) (Ω := SeparableClosure K₁) F₁
    let : HasPrincipalDivisors k₁ F₁ :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k₁ K₁ F₁).toHasPrincipalDivisors
    let : Algebra k₂ (SeparableClosure K₂) :=
      ((algebraMap K₂ (SeparableClosure K₂)).comp (algebraMap k₂ K₂)).toAlgebra
    let : Algebra (RatFunc k₂) (SeparableClosure K₂) :=
      ((algebraMap K₂ (SeparableClosure K₂)).comp (algebraMap (RatFunc k₂) K₂)).toAlgebra
    let : IsScalarTower k₂ K₂ (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower (RatFunc k₂) K₂ (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower k₂ (RatFunc k₂) (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K₂ (SeparableClosure K₂))
        (IsScalarTower.algebraMap_apply k₂ (RatFunc k₂) K₂ x))
    let : FiniteDimensional K₂ F₂ :=
      abstractFixedField_finiteDimensional K₂ (SeparableClosure K₂) H₂.field H₂.finite
    let : FunctionField k₂ F₂ :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k₂) (K := K₂) (Ω := SeparableClosure K₂) F₂
    let : HasPrincipalDivisors k₂ F₂ :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k₂ K₂ F₂).toHasPrincipalDivisors
    ∀ (ε₁ : SeparableClosure F₁ ≃ₐ[F₁] SeparableClosure K₁)
      (ε₂ : SeparableClosure F₂ ≃ₐ[F₂] SeparableClosure K₂)
      (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
      (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
      (e : Place k₁ K₁ ≃ Place k₂ K₂)
      (eF : Place k₁ F₁ ≃ Place k₂ F₂),
    let M₁ := rayModulusBaseChange F₁ m₁
    let M₂ := rayModulusBaseChange F₂ m₂
    ∀ (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
        (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
      (Γ : (localAbsoluteAbelianProfinite F₁ ⧸ artinRaySubgroup M₁) ≃*
        (localAbsoluteAbelianProfinite F₂ ⧸ artinRaySubgroup M₂))
      (hclosure : ∀ v g,
        g ∈ (localRayAbsoluteArtin m₁ v).range.topologicalClosure ↔
          γ g ∈ (localRayAbsoluteArtin m₂ (e v)).range.topologicalClosure)
      (hdegree : ∀ g, rayAbelianDegree m₂ (γ g) = rayAbelianDegree m₁ g)
      (hclosureF : ∀ w g,
        g ∈ (localRayAbsoluteArtin M₁ w).range.topologicalClosure ↔
          Γ g ∈ (localRayAbsoluteArtin M₂ (eF w)).range.topologicalClosure)
      (hdegreeF : ∀ g, rayAbelianDegree M₂ (Γ g) = rayAbelianDegree M₁ g)
      (hboundary₁ : ∀ v : Place k₁ K₁, ∃ z : Place k₁ K₁, z ≠ v ∧ m₁ z ≠ 0)
      (hboundary₂ : ∀ v : Place k₂ K₂, ∃ z : Place k₂ K₂, z ≠ v ∧ m₂ z ≠ 0),
    let hbF₁ := rayModulusBaseChange_other_boundary (L := F₁) m₁ hboundary₁
    let hbF₂ := rayModulusBaseChange_other_boundary (L := F₂) m₂ hboundary₂
    let τ₁ := nativeRayTransferOfFixedField k₁ K₁ H₁ ε₁ m₁ hm₁
    let τ₂ := nativeRayTransferOfFixedField k₂ K₂ H₂ ε₂ m₂ hm₂
    ∀ (_ : ∀ w : Place k₁ F₁, (eF w).restrict K₂ = e (w.restrict K₁))
      (_ : ∀ w : Place k₁ F₁,
        w.ramificationIndex K₁ = (eF w).ramificationIndex K₂)
      (_ : ∀ g, Γ (τ₁ g) = τ₂ (γ g)),
    ∀ (hmzero₁ : m₁ ≠ 0) (hmzero₂ : m₂ ≠ 0),
    let η₀ := reconstructedRayFunction m₁ m₂ e γ
      hclosure hdegree hboundary₁ hboundary₂ hmzero₁ hmzero₂
    let ηF₀ := reconstructedRayFunction M₁ M₂ eF Γ
      hclosureF hdegreeF hbF₁ hbF₂
      (rayModulusBaseChange_ne_zero m₁ hmzero₁) (rayModulusBaseChange_ne_zero m₂ hmzero₂)
    ∀ x : K₁,
    ηF₀ (algebraMap K₁ F₁ x) = algebraMap K₂ F₂ (η₀ x) := by
  intro F₁ F₂ ak₁Ω aR₁Ω hk₁K₁Ω hR₁K₁Ω hk₁R₁Ω hK₁F₁ hF₁field hF₁principal
    ak₂Ω aR₂Ω hk₂K₂Ω hR₂K₂Ω hk₂R₂Ω hK₂F₂ hF₂field hF₂principal
    ε₁ ε₂ m₁ m₂ hm₁ hm₂ e eF M₁ M₂ γ Γ hclosure hdegree hclosureF hdegreeF
    hboundary₁ hboundary₂ hbF₁ hbF₂ τ₁ τ₂ hplaces hindex htransfer hmzero₁ hmzero₂ η₀ ηF₀ x
  have hlowerNative :=
    restrictedProductAbsoluteArtin_baseChange_nativeTransfer k₁ K₁ H₁ ε₁ m₁ hm₁
  have hlower := nativeReciprocitySquare
    (h := nativeRayTransferOfFixedField k₁ K₁ H₁ ε₁ m₁ hm₁)
    (s := restrictedProductAbsoluteArtin m₁) hlowerNative
  have hupperNative :=
    restrictedProductAbsoluteArtin_baseChange_nativeTransfer k₂ K₂ H₂ ε₂ m₂ hm₂
  have hupper := nativeReciprocitySquare
    (h := nativeRayTransferOfFixedField k₂ K₂ H₂ ε₂ m₂ hm₂)
    (s := restrictedProductAbsoluteArtin m₂) hupperNative
  exact reconstructedRayFunction_baseChange_core (L₁ := F₁) (L₂ := F₂)
    (m₁ := m₁) (m₂ := m₂) (hm₁ := hm₁) (hm₂ := hm₂) (e := e) (eF := eF)
    (γ := γ) (Γ := Γ) (hclosure := hclosure) (hdegree := hdegree)
    (hclosureF := hclosureF) (hdegreeF := hdegreeF)
    (hboundary₁ := hboundary₁) (hboundary₂ := hboundary₂)
    (τ₁ := τ₁) (τ₂ := τ₂) (hplaces := hplaces) (hindex := hindex)
    (htransfer := htransfer)
    (hlower := hlower) (hupper := hupper)
    (hmzero₁ := hmzero₁) (hmzero₂ := hmzero₂) x

end FunctionField.RayClass
