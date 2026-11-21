/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicReciprocityCorestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalInvariant
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramifiedEquiv

/-! # Arithmetic evaluation of a cyclic Brauer class at an unramified stage -/

@[expose] public section

noncomputable section

open CategoryTheory LocalClassFieldTheory LocalFieldTheory Module
open ClassFieldTower.Cohomology LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

/-- The continuous local Artin map is invariant under finite extension conjugation. -/
private theorem abelianLocalArtinMap_autCongr_apply
    (F L M : Type u) [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [FiniteDimensional F L] [FiniteDimensional F M] [IsAbelianGalois F L] [IsAbelianGalois F M]
    (c : L ≃ₐ[F] M) (b : Fˣ) :
    AlgEquiv.autCongr c (abelianLocalArtinMap F L b) = abelianLocalArtinMap F M b := by
  have hc := DFunLike.congr_fun (abelianLocalArtinMonoidHom_autCongr F L M c) b
  simp only [← abelianLocalArtinMap_toMonoidHom] at hc
  exact hc

private theorem finiteCyclicArithmeticCharacter_inv_congr
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (p : H ≃* G) (hgen : p h = g) (a : G) (b : H) (hab : p b = a) :
    finiteCyclicArithmeticCharacter h hh (Additive.ofMul b⁻¹) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul a⁻¹) := by
  rw [← hab, ← map_inv]
  exact (finiteCyclicArithmeticCharacter_map_of_generator_power g hg h hh p.toMonoidHom 1
    (by decide) (by rw [one_mul]; exact Nat.card_congr p.symm.toEquiv)
    (by rw [pow_one]; exact hgen) _).symm

section UnramifiedEvaluation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (D : FiniteGaloisIntermediateField F (SeparableClosure F))

@[reducible] local instance arithmeticStageAlgebra :
    Algebra F ↥D.toIntermediateField := finiteGaloisStageAlgebra D

local instance : NontriviallyNormedField ↥D.toIntermediateField :=
  finiteExtensionSpectralNormedField F ↥D.toIntermediateField
local instance : ValuativeRel ↥D.toIntermediateField :=
  finiteExtensionSpectralValuativeRel F ↥D.toIntermediateField
local instance : IsNonarchimedeanLocalField ↥D.toIntermediateField :=
  finiteExtensionSpectralIsNonarchimedeanLocalField F ↥D.toIntermediateField
local instance : Valuation.HasExtension (ValuativeRel.valuation F)
    (ValuativeRel.valuation ↥D.toIntermediateField) :=
  finiteExtensionSpectralValuation_hasExtension F ↥D.toIntermediateField
local instance : IsIntegralClosure 𝒪[↥D.toIntermediateField] 𝒪[F] ↥D.toIntermediateField :=
  localCompleteDVF_integerRing_isIntegralClosure F ↥D.toIntermediateField
local instance : Module.Finite 𝒪[F] 𝒪[↥D.toIntermediateField] :=
  localCompleteDVF_integerRing_moduleFinite F ↥D.toIntermediateField

section ArithmeticEvaluation

variable [IsAbelianGalois F ↥D.toIntermediateField] [IsCyclic Gal(↥D.toIntermediateField/F)]

/-- The inflated cyclic class uses the same Artin value as its unramified representative. -/
private theorem unramifiedCyclicBrauerInvariant_eq_artin
    [IsUnramifiedValuedExtension F ↥D.toIntermediateField]
    (g : Gal(↥D.toIntermediateField/F)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) (b : Fˣ) :
    localBrauerInvariant F (cyclicBrauerClass D g hg b) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul ((abelianLocalArtinMap F D b)⁻¹)) := by
  let y := cyclicContinuousUnitClass F D g hg (Additive.ofMul b)
  exact (localBrauerInvariant_finiteInflation_of_unramified F D y).trans
    (unramifiedContinuousInvariant_cyclicClass_eq_artin F D g hg b)

private theorem unramifiedCyclicBrauerInvariant_eq_artin_of_algEquiv
    (C : Type u) [Field C] [Algebra F C] [FiniteDimensional F C]
    [ValuativeRel C] [TopologicalSpace C] [IsNonarchimedeanLocalField C]
    [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation C)]
    [IsIntegralClosure 𝒪[C] 𝒪[F] C] [Module.Finite 𝒪[F] 𝒪[C]]
    [IsUnramifiedValuedExtension F C] (c : (↥D.toIntermediateField) ≃ₐ[F] C)
    (g : Gal(↥D.toIntermediateField/F)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) (b : Fˣ) :
    localBrauerInvariant F (cyclicBrauerClass D g hg b) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul ((abelianLocalArtinMap F D b)⁻¹)) := by
  let : IsUnramifiedValuedExtension F ↥D.toIntermediateField :=
    ClassFieldTower.Martinet.Shafarevich.isUnramifiedValuedExtension_of_algEquiv
      F ↥D.toIntermediateField C c
  exact unramifiedCyclicBrauerInvariant_eq_artin F D g hg b

private theorem unramifiedCyclicBrauerInvariant_conjugateValues
    (C : Type u) [Field C] [Algebra F C] [FiniteDimensional F C]
    [ValuativeRel C] [TopologicalSpace C] [IsNonarchimedeanLocalField C]
    [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation C)]
    [IsIntegralClosure 𝒪[C] 𝒪[F] C] [Module.Finite 𝒪[F] 𝒪[C]]
    [IsUnramifiedValuedExtension F C] [IsAbelianGalois F C]
    {G : Type u} [Group G] (c : (↥D.toIntermediateField) ≃ₐ[F] C)
    (e : Gal(C/F) ≃* G) (h : Gal(↥D.toIntermediateField/F))
    (hh : ∀ x, x ∈ Subgroup.zpowers h) (b : Fˣ) (σ : G)
    (hArtin : abelianLocalArtinMap F C b = e.symm σ) :
    ((AlgEquiv.autCongr c).trans e) (abelianLocalArtinMap F D b) = σ ∧
      localBrauerInvariant F (cyclicBrauerClass D h hh b) =
        finiteCyclicArithmeticCharacter h hh (Additive.ofMul ((abelianLocalArtinMap F D b)⁻¹)) := by
  refine ⟨?_, unramifiedCyclicBrauerInvariant_eq_artin_of_algEquiv F D C c h hh b⟩
  exact (congrArg e (abelianLocalArtinMap_autCongr_apply F ↥D.toIntermediateField C c b)).trans
    ((congrArg e hArtin).trans (e.apply_symm_apply σ))

end ArithmeticEvaluation

/-- The arithmetic invariant at a compatible cyclic stage, with its specified generator. -/
structure CyclicArtinEvaluation {G : Type u} [Group G] [Fintype G]
    (q : Gal(↥D.toIntermediateField/F) ≃* G)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (b : Fˣ) (σ : G) where
  /-- The source finite Galois group is cyclic. -/
  cyclic : IsCyclic Gal(↥D.toIntermediateField/F)
  /-- The generator obtained from the specified target generator. -/
  generator : Gal(↥D.toIntermediateField/F)
  /-- The chosen source element generates its Galois group. -/
  generates : ∀ x, x ∈ Subgroup.zpowers generator
  /-- The compatible group isomorphism sends the generator to the target. -/
  generator_map : q generator = g
  /-- The local invariant equals the arithmetic character at the inverse symbol. -/
  invariant_eq :
    let : IsCyclic Gal(↥D.toIntermediateField/F) := cyclic
    localBrauerInvariant F (cyclicBrauerClass D generator generates b) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul σ⁻¹)

/-- Evaluate the cyclic invariant using the chosen unramified field isomorphism. -/
theorem nonempty_cyclicArtinEvaluation_of_algEquiv
    (B : Type u) [Field B] [Algebra F B] [FiniteDimensional F B]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation B)]
    [IsIntegralClosure 𝒪[B] 𝒪[F] B] [Module.Finite 𝒪[F] 𝒪[B]]
    [IsUnramifiedValuedExtension F B] [IsAbelianGalois F B]
    {G : Type u} [Group G] [Fintype G] [IsCyclic G] (c : (↥D.toIntermediateField) ≃ₐ[F] B)
    (e : Gal(B/F) ≃* G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (b : Fˣ) (σ : G) (hs : abelianLocalArtinMap F B b = e.symm σ) :
    Nonempty (CyclicArtinEvaluation F D ((AlgEquiv.autCongr c).trans e) g hg b σ) := by
  let q : Gal(↥D.toIntermediateField/F) ≃* G := (AlgEquiv.autCongr c).trans e
  let h := q.symm g
  have hh := LocalClassFieldTheory.map_cyclicGenerator q.symm g hg
  let hcyc : IsCyclic Gal(↥D.toIntermediateField/F) := q.isCyclic.mpr inferInstance
  let hab : IsAbelianGalois F ↥D.toIntermediateField :=
    IsAbelianGalois.of_isCyclic F ↥D.toIntermediateField
  have values := unramifiedCyclicBrauerInvariant_conjugateValues F D B c e h hh b σ hs
  have hgen : q h = g := q.apply_symm_apply g
  exact ⟨⟨hcyc, h, hh, hgen, values.2.trans
    (finiteCyclicArithmeticCharacter_inv_congr g hg h hh q hgen σ _ values.1)⟩⟩

end UnramifiedEvaluation

end ClassFieldTheory.Brauer
