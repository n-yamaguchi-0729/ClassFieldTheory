/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum
public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.Algebra.Brauer.DiscreteRelative
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanNormQuotient
public import Nyll.GaloisCohomology.Topology.FieldIsomorphismClosure

/-! # The real Brauer invariant -/

@[expose] public section

noncomputable section

open CategoryTheory ClassFieldTower.Cohomology LocalClassFieldTheory LocalFieldTheory

namespace ClassFieldTheory.Brauer

universe u

local instance : IsSepClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩

private theorem realGalois_card : Nat.card Gal(ℂ/ℝ) = 2 :=
  (IsGalois.card_aut_eq_finrank ℝ ℂ).trans Complex.finrank_real_complex

local instance : IsCyclic Gal(ℂ/ℝ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCyclic_of_prime_card realGalois_card

/-- Complex conjugation generates the actual Galois group of the reals. -/
theorem complexConjugation_generates (σ : Gal(ℂ/ℝ)) :
    σ ∈ Subgroup.zpowers Complex.conjAe := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply mem_zpowers_of_prime_card realGalois_card
  intro h
  have hI := congrArg (fun g : Gal(ℂ/ℝ) => (g Complex.I).im) h
  change -(1 : ℝ) = 1 at hI
  norm_num at hI

/-- The actual degree-two carry class of a real unit for complex conjugation. -/
def realUnitClass : Additive ℝˣ →+ groupCohomology (liftedGaloisUnitsRep ℝ ℂ) 2 :=
  cyclicUnitClass ℝ ℂ Complex.conjAe complexConjugation_generates

/-- Every ordinary real degree-two class comes from a real unit. -/
theorem realUnitClass_surjective : Function.Surjective realUnitClass :=
  cyclicUnitClass_surjective ℝ ℂ Complex.conjAe complexConjugation_generates

/-- The actual unit class and the real sign have the same kernel. -/
theorem realUnitClass_ker : realUnitClass.ker = realUnitsSign.toAdditive.ker := by
  ext a
  change realUnitClass (Additive.ofMul a.toMul) = 0 ↔ realUnitsSign a.toMul = 1
  rw [realUnitClass, cyclicUnitClass_eq_zero_iff_norm, ← realUnitsSign_ker_eq_complexNormSubgroup]
  exact MonoidHom.mem_ker

/-- The ordinary real degree-two group identifies its actual unit class with its sign. -/
def realCohomologySignEquiv :
    groupCohomology (liftedGaloisUnitsRep ℝ ℂ) 2 ≃+ Additive ℤˣ :=
  (QuotientAddGroup.quotientKerEquivOfSurjective realUnitClass realUnitClass_surjective).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq realUnitClass_ker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective realUnitsSign.toAdditive
        realUnitsSign_surjective))

@[simp]
theorem realCohomologySignEquiv_class (a : ℝˣ) :
    realCohomologySignEquiv (realUnitClass (Additive.ofMul a)) =
      Additive.ofMul (realUnitsSign a) := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective realUnitClass realUnitClass_surjective
  have he : e.symm (realUnitClass (Additive.ofMul a)) = QuotientAddGroup.mk (Additive.ofMul a) := by
    apply e.injective
    exact e.apply_symm_apply (realUnitClass (Additive.ofMul a))
  change (QuotientAddGroup.quotientKerEquivOfSurjective realUnitsSign.toAdditive
    realUnitsSign_surjective)
      (QuotientAddGroup.quotientAddEquivOfEq realUnitClass_ker
        (e.symm (realUnitClass (Additive.ofMul a)))) = _
  let q := QuotientAddGroup.quotientAddEquivOfEq realUnitClass_ker
  have hq := (congrArg (fun y => q y) he).trans
    (QuotientAddGroup.quotientAddEquivOfEq_mk realUnitClass_ker (Additive.ofMul a))
  exact congrArg (fun y => QuotientAddGroup.quotientKerEquivOfSurjective
    realUnitsSign.toAdditive realUnitsSign_surjective y) hq

/-- The same sign comparison for a field equipped with its actual real coordinate. -/
def realBrauerSignEquivOfRingEquiv {F : Type u} [Field F] (e : F ≃+* ℝ) :
    Br F ≃+ Additive ℤˣ := by
  let Ω := SeparableClosure F
  let eΩ := GaloisCohomology.suppliedFieldIsoClosureEquiv e Ω ℂ
  have hΩ (x : F) : eΩ (algebraMap F Ω x) = algebraMap ℝ ℂ (e x) :=
    GaloisCohomology.suppliedFieldIsoClosureEquiv_algebraMap e Ω ℂ x
  have hcomp : (algebraMap ℝ ℂ).comp e.toRingHom = eΩ.toRingHom.comp (algebraMap F Ω) :=
    RingHom.ext (fun x => (hΩ x).symm)
  have hdeg : Module.finrank F Ω = 2 :=
    (Algebra.finrank_eq_of_equiv_equiv e eΩ hcomp).trans Complex.finrank_real_complex
  let : FiniteDimensional F Ω := FiniteDimensional.of_finrank_pos (hdeg.symm ▸ Nat.zero_lt_two)
  have hcard : Nat.card Gal(Ω/F) = 2 := (IsGalois.card_aut_eq_finrank F Ω).trans hdeg
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic Gal(Ω/F) := isCyclic_of_prime_card hcard
  let g : Gal(Ω/F) :=
    { __ := (eΩ.trans Complex.conjAe.toRingEquiv).trans eΩ.symm
      commutes' x := by
        apply eΩ.injective
        change eΩ (eΩ.symm (Complex.conjAe (eΩ (algebraMap F Ω x)))) = eΩ (algebraMap F Ω x)
        rw [eΩ.apply_symm_apply, hΩ, Complex.conjAe.commutes] }
  have hgne : g ≠ 1 := by
    intro h
    have hI := congrArg (fun a : Gal(Ω/F) => (eΩ (a (eΩ.symm Complex.I))).im) h
    change (eΩ (eΩ.symm (Complex.conjAe (eΩ (eΩ.symm Complex.I))))).im =
      (eΩ (eΩ.symm Complex.I)).im at hI
    simp only [eΩ.apply_symm_apply] at hI
    change -(1 : ℝ) = 1 at hI
    norm_num at hI
  have hgen (σ : Gal(Ω/F)) : σ ∈ Subgroup.zpowers g := mem_zpowers_of_prime_card hcard hgne
  let normComparison :=
    (normQuotientEquivOfRingEquiv e eΩ hcomp).trans realComplexNormQuotientEquivSign
  exact (continuousRelativeUnitsH2Equiv F Ω).trans
    ((cyclicUnitH2NormEquiv F Ω g hgen).trans normComparison.toAdditive)

/-- The actual continuous Brauer group of the reals is the two-element sign group. -/
def realBrauerSignEquiv : Br ℝ ≃+ Additive ℤˣ :=
  realBrauerSignEquivOfRingEquiv (RingEquiv.refl ℝ)

end ClassFieldTheory.Brauer
