/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicReciprocityArithmetic
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicReciprocityCorestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicUnramifiedDiagonal
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.EmbeddedCorestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClass
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramifiedEquiv

/-! # The cyclic Brauer invariant and the local reciprocity symbol -/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

noncomputable section

open CategoryTheory LocalClassFieldTheory LocalFieldTheory Module
open ClassFieldTower.Cohomology LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

section ClosureDiagram

variable (K : Type u) [Field K]
  (F C : IntermediateField K (SeparableClosure K)) [Algebra F C]
  [FiniteDimensional F C] [IsGalois F C]

local notation "Ω" => SeparableClosure K

attribute [local instance] stageSeparableClosureAlgebra

@[reducible] local instance diagonalFieldRangeAlgebra
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F))) :
    Algebra (↥F) (↥D.toIntermediateField) := finiteGaloisStageAlgebra D

/-- The upper separable closure contains the original embedded stage with its original values. -/
private theorem exists_diagonalStageFieldRangeComparison
    (hFC : ∀ x : F, C.val (algebraMap F C x) = (x : Ω)) :
    ∃ (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
      (j : Ω ≃ₐ[↥F] SeparableClosure (↥F))
      (c : (↥C) ≃ₐ[↥F] (↥D.toIntermediateField)),
      ∀ y : C, D.toIntermediateField.val (c y) = j (C.val y) := by
  let : Algebra.IsSeparable F Ω := Algebra.isSeparable_tower_top_of_isSeparable K F Ω
  let : IsSepClosure F Ω := ⟨inferInstance, inferInstance⟩
  let j : Ω ≃ₐ[↥F] SeparableClosure (↥F) := IsSepClosure.equiv F Ω (SeparableClosure F)
  let i : C →ₐ[F] SeparableClosure F :=
    { __ := j.toRingEquiv.toRingHom.comp C.val.toRingHom
      commutes' := fun x => (congrArg j (hFC x)).trans (j.commutes x) }
  let D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)) := i.finiteGaloisFieldRange
  let c : (↥C) ≃ₐ[↥F] (↥D.toIntermediateField) := i.equivFieldRange
  exact ⟨D, j, c, fun _ => rfl⟩

end ClosureDiagram

section DiagonalCoordinates

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]

local notation "C" => cyclicLocalUnramifiedCompositum K L

variable (H : Subgroup (Gal(↥(cyclicLocalUnramifiedCompositum K L)/K)))

local notation "F" => cyclicLocalDiagonalField K L H

local instance : Algebra F C := cyclicLocalDiagonalAlgebra K L H

local instance : Algebra L C :=
  (L.inclusion (show L ≤ C from le_sup_left)).toRingHom.toAlgebra
local instance : IsScalarTower K L C := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower K F C :=
  IsScalarTower.of_algebraMap_eq' (R := K) (S := F) (A := C) rfl

/-- The original Galois map evaluates on the same field element in the compositum. -/
private theorem cyclicLocalDiagonalGaloisEquiv_apply_ambient
    (hmap : Subgroup.map (cyclicLocalOriginalRestriction K L) H = (⊤ : Subgroup Gal(L/K)))
    (hdegree : Module.finrank (IntermediateField.fixedField H) C = Module.finrank K L)
    (τ : Gal(C/F)) (x : L) :
    IntermediateField.val C (τ (algebraMap L C x)) =
      L.val (cyclicLocalDiagonalGaloisEquiv K L H hmap hdegree τ x) := by
  rw [cyclicLocalDiagonalGaloisEquiv_apply]
  have h := (τ.restrictScalars K).restrictNormal_commutes L x
  exact congrArg (IntermediateField.val C) h.symm

end DiagonalCoordinates

section DiagonalRestriction

variable (K : Type u) [Field K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K))
  (F C : IntermediateField K (SeparableClosure K)) [Algebra F C]
  [Algebra (↥E.toIntermediateField) C]

local notation "Ω" => SeparableClosure K

attribute [local instance] stageSeparableClosureAlgebra

@[reducible] local instance diagonalRangeAlgebra
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F))) :
    Algebra (↥F) (↥D.toIntermediateField) := finiteGaloisStageAlgebra D

private theorem diagonalRangeRestriction_apply
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
    (j : Ω ≃ₐ[↥F] SeparableClosure (↥F))
    (c : (↥C) ≃ₐ[↥F] (↥D.toIntermediateField))
    (hc : ∀ y : C, D.toIntermediateField.val (c y) = j (C.val y))
    (e : Gal(C/F) ≃* Gal(E/K))
    (hEC : ∀ (σ : Gal(C/F)) (x : E),
      C.val (σ (algebraMap E C x)) = E.toIntermediateField.val (e σ x))
    (σ : Gal(SeparableClosure F/F)) :
    finiteGaloisRestriction E (embeddedAbsoluteRestrictionHom K F j σ) =
      e (AlgEquiv.autCongr c.symm (finiteGaloisRestriction D σ)) := by
  let τ := AlgEquiv.autCongr c.symm (finiteGaloisRestriction D σ)
  have hτ (y : C) : j (C.val (τ y)) = σ (j (C.val y)) := by
    calc
      j (C.val (τ y)) = D.toIntermediateField.val (c (τ y)) := (hc (τ y)).symm
      _ = D.toIntermediateField.val (finiteGaloisRestriction D σ (c y)) :=
        congrArg D.toIntermediateField.val (c.apply_symm_apply _)
      _ = σ (D.toIntermediateField.val (c y)) := finiteGaloisRestriction_commutes D σ (c y)
      _ = σ (j (C.val y)) := congrArg σ (hc y)
  apply AlgEquiv.ext
  intro x
  apply (j.toRingEquiv.toRingHom.comp E.toIntermediateField.val.toRingHom).injective
  have hx : C.val (algebraMap E C x) = E.toIntermediateField.val x := by
    simpa only [map_one, AlgEquiv.one_apply] using hEC 1 x
  calc
    j (E.toIntermediateField.val (finiteGaloisRestriction E
        (embeddedAbsoluteRestrictionHom K F j σ) x)) =
        σ (j (E.toIntermediateField.val x)) :=
      (congrArg j (finiteGaloisRestriction_commutes E
        (embeddedAbsoluteRestrictionHom K F j σ) x)).trans
        (embeddedAbsoluteRestrictionHom_commutes K F j σ (E.toIntermediateField.val x))
    _ = σ (j (C.val (algebraMap E C x))) := congrArg (fun z => σ (j z)) hx.symm
    _ = j (C.val (τ (algebraMap E C x))) := (hτ (algebraMap E C x)).symm
    _ = j (E.toIntermediateField.val (e τ x)) := congrArg j (hEC τ x)

end DiagonalRestriction

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K))
  [IsCyclic Gal(E/K)] [IsAbelianGalois K E]
  (g : Gal(E/K)) (hg : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers g)

private def cyclicInvariantMatchesArtin (a : Kˣ) : Prop :=
  localBrauerInvariant K (cyclicBrauerClass E g hg a) =
    finiteCyclicArithmeticCharacter g hg (Additive.ofMul ((abelianLocalArtinMap K E a)⁻¹))

section DiagonalStage

local notation "Ω" => SeparableClosure K

attribute [local instance] stageSeparableClosureAlgebra
attribute [local instance] embeddedStageSpectralNormedField embeddedStageSpectralValuativeRel
  embeddedStageSpectralLocalField

variable (F C : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K F] [FiniteDimensional K C] [Algebra F C] [IsScalarTower K F C]
  [FiniteDimensional F C] [relativeAbelian : IsAbelianGalois F C]
  [Algebra (↥E.toIntermediateField) C]
  [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation C)]
  [IsIntegralClosure 𝒪[C] 𝒪[F] C] [Module.Finite 𝒪[F] 𝒪[C]]
  [IsUnramifiedValuedExtension F C]

attribute [local instance] diagonalRangeAlgebra

private theorem cyclicInvariant_eq_artin_of_evaluated_range
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
    (j : Ω ≃ₐ[↥F] SeparableClosure (↥F))
    (q : Gal(↥D.toIntermediateField/↥F) ≃* Gal(E/K))
    (hp : ∀ σ, finiteGaloisRestriction E (embeddedAbsoluteRestrictionHom K F j σ) =
      q (finiteGaloisRestriction D σ))
    (a : Kˣ) (b : Fˣ)
    (hnorm : abelianLocalArtinMap K E (normUnits K F b) = abelianLocalArtinMap K E a)
    (t : CyclicArtinEvaluation F D q g hg b (abelianLocalArtinMap K E a)) :
    cyclicInvariantMatchesArtin K E g hg a := by
  let : IsCyclic Gal(↥D.toIntermediateField/↥F) := t.cyclic
  unfold cyclicInvariantMatchesArtin
  exact cyclicInvariant_eq_of_unramified_comparison K E g hg F D j q
    t.generator t.generates t.generator_map hp a b hnorm t.invariant_eq

private theorem cyclicInvariant_eq_artin_of_conjugated_unramified_stage
    (B : Type u) [Field B] [Algebra F B] [FiniteDimensional F B] [IsAbelianGalois F B]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation B)]
    [IsIntegralClosure 𝒪[B] 𝒪[F] B] [Module.Finite 𝒪[F] 𝒪[B]]
    [IsUnramifiedValuedExtension F B]
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
    (j : Ω ≃ₐ[↥F] SeparableClosure (↥F))
    (c : B ≃ₐ[↥F] (↥D.toIntermediateField)) (e : Gal(B/F) ≃* Gal(E/K))
    (hp : ∀ σ, finiteGaloisRestriction E (embeddedAbsoluteRestrictionHom K F j σ) =
      e (AlgEquiv.autCongr c.symm (finiteGaloisRestriction D σ)))
    (a : Kˣ) (b : Fˣ)
    (hnorm : abelianLocalArtinMap K E (normUnits K F b) = abelianLocalArtinMap K E a)
    (hupper : abelianLocalArtinMap F B b = e.symm (abelianLocalArtinMap K E a)) :
    cyclicInvariantMatchesArtin K E g hg a := by
  let p : Gal(↥D.toIntermediateField/↥F) ≃* Gal(E/K) := (AlgEquiv.autCongr c.symm).trans e
  obtain ⟨t⟩ := nonempty_cyclicArtinEvaluation_of_algEquiv F D B c.symm e g hg b
    (abelianLocalArtinMap K E a) hupper
  exact cyclicInvariant_eq_artin_of_evaluated_range K E g hg F D j p hp a b hnorm t

omit [IsScalarTower K F C] in
/-- The unramified calculation after transporting through the exact embedded Galois stage. -/
private theorem cyclicInvariant_eq_artin_of_diagonal_range
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
    (j : Ω ≃ₐ[↥F] SeparableClosure (↥F))
    (c : (↥C) ≃ₐ[↥F] (↥D.toIntermediateField))
    (hc : ∀ y : C, D.toIntermediateField.val (c y) = j (C.val y))
    (e : Gal(C/F) ≃* Gal(E/K))
    (hEC : ∀ (σ : Gal(C/F)) (x : E),
      C.val (σ (algebraMap E C x)) = E.toIntermediateField.val (e σ x))
    (a : Kˣ) (b : Fˣ)
    (hnorm : abelianLocalArtinMap K E (normUnits K F b) = abelianLocalArtinMap K E a)
    (hupper : abelianLocalArtinMap F C b = e.symm (abelianLocalArtinMap K E a)) :
    cyclicInvariantMatchesArtin K E g hg a :=
  cyclicInvariant_eq_artin_of_conjugated_unramified_stage K E g hg F C D j c e
    (diagonalRangeRestriction_apply K E F C D j c hc e hEC) a b hnorm hupper

omit [IsScalarTower K F C] in
private theorem cyclicInvariant_eq_artin_of_diagonal_stage
    (e : Gal(C/F) ≃* Gal(E/K))
    (hFC : ∀ x : F, C.val (algebraMap F C x) = (x : Ω))
    (hEC : ∀ (σ : Gal(C/F)) (x : E),
      C.val (σ (algebraMap E C x)) = E.toIntermediateField.val (e σ x))
    (a : Kˣ) (b : Fˣ)
    (hnorm : abelianLocalArtinMap K E (normUnits K F b) = abelianLocalArtinMap K E a)
    (hupper : abelianLocalArtinMap F C b = e.symm (abelianLocalArtinMap K E a)) :
    cyclicInvariantMatchesArtin K E g hg a := by
  let : IsGalois F C := relativeAbelian.toIsGalois
  obtain ⟨D, j, c, hc⟩ := exists_diagonalStageFieldRangeComparison K F C hFC
  exact cyclicInvariant_eq_artin_of_diagonal_range K E g hg F C D j c
    hc e hEC a b hnorm hupper

end DiagonalStage

private theorem cyclicInvariant_eq_artin_of_chosen_diagonal
    (H : Subgroup Gal(cyclicLocalUnramifiedCompositum K E.toIntermediateField/K))
    (hmap : H.map (cyclicLocalOriginalRestriction K E.toIntermediateField) =
      (⊤ : Subgroup Gal(E/K)))
    (hU : Function.Injective ((cyclicLocalUnramifiedRestriction K E.toIntermediateField).comp
      H.subtype))
    (hdegree : Module.finrank (IntermediateField.fixedField H)
        (cyclicLocalUnramifiedCompositum K E.toIntermediateField) = Module.finrank K E)
    (a : Kˣ) :
    cyclicInvariantMatchesArtin K E g hg a := by
  let L := E.toIntermediateField
  let C := cyclicLocalUnramifiedCompositum K L
  let F := cyclicLocalDiagonalField K L H
  let := cyclicCompositumFinite K L
  let := cyclicDiagonalBaseFinite K L H
  let := cyclicLocalDiagonalAlgebra K L H
  let := cyclicDiagonalScalarTower K L H
  let := cyclicDiagonalRelativeFinite K L H
  let := cyclicDiagonalRelativeGalois K L H
  let := (cyclicDiagonalRelativeGalois K L H).to_isSeparable
  let := cyclicDiagonalBaseNormedField K L H
  let := cyclicDiagonalBaseValuativeRel K L H
  let := cyclicDiagonalBaseLocalField K L H
  let := cyclicCompositumNormedField K L
  let := cyclicCompositumValuativeRel K L
  let := cyclicCompositumLocalField K L
  let := cyclicDiagonalValuationExtension K L H
  let := localCompleteDVF_integerRing_isIntegralClosure F C
  let := cyclicDiagonalIntegerRingFinite K L H
  let e := cyclicLocalDiagonalGaloisEquiv K L H hmap hdegree
  let := cyclicLocalDiagonalRelative_isAbelianGalois K L H e
  let := cyclicLocalUnramifiedDiagonal_isUnramified K L H hU
  let σ := abelianLocalArtinMap K E a
  obtain ⟨b, hnorm, hupper⟩ := exists_cyclicLocalDiagonalArtinNorm K L H hmap hdegree σ
  let : Algebra L C := (L.inclusion (show L ≤ C from le_sup_left)).toRingHom.toAlgebra
  let : IsScalarTower K L C := IsScalarTower.of_algebraMap_eq' rfl
  have heC (τ : Gal(C/F)) (x : E) :=
    cyclicLocalDiagonalGaloisEquiv_apply_ambient K L H hmap hdegree τ x
  have hFC (x : F) : C.val (algebraMap F C x) = (x : SeparableClosure K) := rfl
  exact cyclicInvariant_eq_artin_of_diagonal_stage K E g hg F C e
    hFC heC a b hnorm hupper

/-- The canonical local invariant of the actual cyclic carry class evaluates
the cyclic character at the arithmetic Artin value of the original unit. -/
theorem localBrauerInvariant_cyclicBrauerClass_eq_artin (a : Kˣ) :
    localBrauerInvariant K (cyclicBrauerClass E g hg a) =
      finiteCyclicArithmeticCharacter g hg
        (Additive.ofMul ((LocalClassFieldTheory.abelianLocalArtinMap K E a)⁻¹)) := by
  obtain ⟨H, hmap, hU, hdegree⟩ := exists_cyclicLocalUnramifiedDiagonal K E.toIntermediateField
  exact cyclicInvariant_eq_artin_of_chosen_diagonal K E g hg H hmap hU.1 hdegree a

/-- A base unit representing the fundamental class has arithmetic Artin
symbol equal to the specified cyclic generator. -/
theorem exists_cyclicFundamentalClass_baseUnit :
    ∃ a : Kˣ, cyclicContinuousUnitClass K E g hg (Additive.ofMul a) = localFundamentalClass K E ∧
      LocalClassFieldTheory.abelianLocalArtinMap K E a = g⁻¹ := by
  let e := continuousRelativeUnitsH2Equiv K E
  obtain ⟨b, hb⟩ := cyclicUnitClass_surjective K E g hg (e (localFundamentalClass K E))
  let a := b.toMul
  have ha :
      cyclicContinuousUnitClass K E g hg (Additive.ofMul a) = localFundamentalClass K E := by
    change e.symm (cyclicUnitClass K E g hg b) = localFundamentalClass K E
    rw [hb, e.symm_apply_apply]
  refine ⟨a, ha, ?_⟩
  have hgen :
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul g) =
        (((1 : ℚ) / (finrank K E : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
    change zmodToRationalCircle (Nat.card Gal(E/K)) Nat.card_pos
      (finiteCyclicGeneratorCoordinate g hg g) = _
    rw [finiteCyclicGeneratorCoordinate_generator]
    simpa only [Int.cast_one, IsGalois.card_aut_eq_finrank] using
      zmodToRationalCircle_intCast (Nat.card Gal(E/K)) Nat.card_pos 1
  have hrec := localBrauerInvariant_cyclicBrauerClass_eq_artin K E g hg a
  change relativeLocalBrauerInvariant K E
    (cyclicContinuousUnitClass K E g hg (Additive.ofMul a)) = _ at hrec
  rw [ha, relativeLocalBrauerInvariant_fundamentalClass, ← hgen] at hrec
  have he := finiteCyclicArithmeticCharacter_injective g hg hrec
  calc
    abelianLocalArtinMap K E a = ((abelianLocalArtinMap K E a)⁻¹)⁻¹ := (inv_inv _).symm
    _ = g⁻¹ := congrArg (fun x : Additive Gal(E/K) => x.toMul⁻¹) he.symm

end ClassFieldTheory.Brauer
