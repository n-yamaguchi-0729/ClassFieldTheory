/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.InvariantTransport
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalInvariant
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison

/-! # The canonical restriction of a local Brauer class is detected by the extension degree -/

@[expose] public section

noncomputable section

open LocalClassFieldTheory LocalFieldTheory
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

private theorem localBrauerInvariant_ringEquiv_chosenClosures
    {P Q : Type u} [Field P] [Field Q]
    [ValuativeRel P] [TopologicalSpace P] [IsNonarchimedeanLocalField P]
    [ValuativeRel Q] [TopologicalSpace Q] [IsNonarchimedeanLocalField Q]
    (e : P ≃+* Q) (hv : SemilinearValuationCompatible P Q e) (x : Br P) :
    localBrauerInvariant Q (restrict e.toRingHom x) = localBrauerInvariant P x := by
  let Ω := SeparableClosure Q
  let : Algebra P Ω := ((algebraMap Q Ω).comp e.toRingHom).toAlgebra
  let : IsSepClosure P Ω := ⟨IsSepClosure.sep_closed Q,
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl Ω) (RingHom.ext fun a => by
      change algebraMap Q Ω (e (e.symm a)) = algebraMap Q Ω a
      rw [e.apply_symm_apply])⟩
  let j := IsSepClosure.equiv P (SeparableClosure P) Ω
  have hj (a : P) : j.toRingEquiv (algebraMap P (SeparableClosure P) a) =
      algebraMap Q Ω (e a) := j.commutes a
  exact localBrauerInvariant_ringEquiv e hv j.toRingEquiv hj x

variable (K L : Type u) [Field K] [Field L] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

section Spectral

attribute [local instance] embeddedStageSpectralNormedField embeddedStageSpectralValuativeRel
  embeddedStageSpectralLocalField

private theorem localBrauerInvariant_restrict_spectral
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] (x : Br K) :
    localBrauerInvariant E (restrict (algebraMap K E) x) =
      Module.finrank K E • localBrauerInvariant K x := by
  let Ω := SeparableClosure K
  let : IsSepClosure E Ω := ⟨IsSepClosure.sep_closed K,
    Algebra.isSeparable_tower_top_of_isSeparable K E Ω⟩
  let : Algebra E (SeparableClosure E) := (separableClosure E (AlgebraicClosure E)).algebra
  let j : Ω ≃ₐ[E] SeparableClosure E := IsSepClosure.equiv E Ω (SeparableClosure E)
  have hj (a : K) :
      j (algebraMap K Ω a) = algebraMap E (SeparableClosure E) (algebraMap K E a) := by
    rw [IsScalarTower.algebraMap_apply K E Ω, j.commutes]
  have hdefault : embeddedAbsoluteBrRestriction K E j = restrict (algebraMap K E) :=
    restrictOfEmbedding_eq_of_extends (algebraMap K E) (embeddedAbsoluteRestrictionHom K E j)
      j.toRingHom hj (embeddedAbsoluteRestrictionHom_commutes K E j)
  rw [← hdefault, localBrauerInvariant_embeddedRestriction]

end Spectral

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
private theorem restrict_algEquiv_comp {E : Type u} [Field E] [Algebra K E]
    (e : L ≃ₐ[K] E) (x : Br K) :
    restrict e.toRingHom (restrict (algebraMap K L) x) = restrict (algebraMap K E) x := by
  have hmap := restrict_comp (algebraMap K L) e.toRingHom
  have he : e.toRingHom.comp (algebraMap K L) = algebraMap K E := RingHom.ext e.commutes
  rw [he] at hmap
  exact DFunLike.congr_fun hmap x

/-- The original restriction along a finite separable extension kills a
local Brauer class exactly when the extension degree kills its invariant. -/
theorem restrict_eq_zero_iff_finrank_nsmul_localBrauerInvariant (x : Br K) :
    restrict (algebraMap K L) x = 0 ↔ Module.finrank K L • localBrauerInvariant K x = 0 := by
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let E := i.fieldRange
  let e : L ≃ₐ[K] E := i.equivFieldRange
  have : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  have hvalue := localBrauerInvariant_restrict_spectral K E x
  rw [← e.toLinearEquiv.finrank_eq] at hvalue
  have hcomp := restrict_algEquiv_comp K L e x
  rw [← hvalue, ← hcomp]
  constructor
  · intro h
    rw [h, map_zero, map_zero]
  · intro h
    apply restrict_injective_of_ringEquiv e.toRingEquiv
    rw [map_zero]
    apply (localBrauerInvariantEquiv E).injective
    exact h.trans (map_zero (localBrauerInvariantEquiv E)).symm

/-- The canonical local invariant multiplies by the degree under restriction
along the original compatible finite separable extension. -/
theorem localBrauerInvariant_restrict [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] (x : Br K) :
    localBrauerInvariant L (restrict (algebraMap K L) x) =
      Module.finrank K L • localBrauerInvariant K x := by
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let E := i.fieldRange
  let e : L ≃ₐ[K] E := i.equivFieldRange
  let : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  have hvalue := localBrauerInvariant_restrict_spectral K E x
  rw [← e.toLinearEquiv.finrank_eq] at hvalue
  have hcomp := restrict_algEquiv_comp K L e x
  let e₀ := e.toRingEquiv
  let : Algebra L E := e₀.toRingHom.toAlgebra
  have hv : SemilinearValuationCompatible L E e₀ := by
    change (ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation E)
    constructor
    rw [Valuation.isEquiv_iff_val_le_one]
    intro a
    change ValuativeRel.valuation L a ≤ 1 ↔ ValuativeRel.valuation E (e₀ a) ≤ 1
    rw [← (ValuativeRel.valuation L).mem_valuationSubring_iff,
      ← (ValuativeRel.valuation E).mem_valuationSubring_iff,
      ← localSeparableValuationSubring_comap_embedding K L i,
      ← localSeparableValuationSubring_comap_embedding K E E.val]
    exact Iff.rfl
  have htransport := localBrauerInvariant_ringEquiv_chosenClosures e₀ hv
    (restrict (algebraMap K L) x)
  rw [← htransport]
  exact (congrArg (localBrauerInvariant E) hcomp).trans hvalue

end ClassFieldTheory.Brauer
