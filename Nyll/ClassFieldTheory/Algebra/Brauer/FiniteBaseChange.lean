/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Tactic.Group
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRepresentative
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureTransport
public import Nyll.GaloisCohomology.Topology.ContinuousH2InnerAction
public import Nyll.GaloisCohomology.Topology.GaloisRestrictionScalars

/-!
# Restriction through a finite stage

When a finite target stage contains the image of the original source stage,
the restriction of absolute cocycles factors through it on both the group
arguments and the unit values.
-/

public section

noncomputable section

universe u

open CategoryTheory ContRepresentation TopRep ContinuousCohomology

namespace ClassFieldTheory.Brauer

section NormalEmbedding

variable {k B E Ω : Type u} [Field k] [Field B] [Field E] [Field Ω]
    [Algebra k B] [Algebra k E] [Algebra k Ω] [Algebra B Ω] [IsScalarTower k B Ω]
    [Normal k E]

/-- Restrict an automorphism to the image of a normal extension through the given embedding. -/
@[expose]
def embeddedGaloisRestriction (j : E →ₐ[k] Ω) : Gal(Ω/B) →ₜ* Gal(E/k) := by
  let : Normal k j.fieldRange := Normal.of_algEquiv j.equivFieldRange
  let restrictBase : Gal(Ω/B) →* Gal(Ω/k) := AlgEquiv.restrictScalarsHom k
  let restrictImage : Gal(Ω/k) →* Gal(j.fieldRange/k) := AlgEquiv.restrictNormalHom j.fieldRange
  let transport := KummerTheory.galoisClosureTransport j.equivFieldRange.symm
  exact
    { toMonoidHom := transport.toMulEquiv.toMonoidHom.comp (restrictImage.comp restrictBase)
      continuous_toFun := transport.continuous.comp
        ((InfiniteGalois.restrictNormalHom_continuous j.fieldRange).comp
          (InfiniteGalois.restrictScalarsHom_continuous k B Ω)) }

/-- The restriction agrees with the original action on embedded field elements. -/
theorem embeddedGaloisRestriction_commutes (j : E →ₐ[k] Ω) (σ : Gal(Ω/B)) (x : E) :
    j (embeddedGaloisRestriction j σ x) = σ (j x) := by
  let : Normal k j.fieldRange := Normal.of_algEquiv j.equivFieldRange
  let τ : Gal(Ω/k) := σ.restrictScalars k
  let a : j.fieldRange := τ.restrictNormal j.fieldRange (j.equivFieldRange x)
  change (j.equivFieldRange (j.equivFieldRange.symm a) : Ω) = σ (j x)
  rw [j.equivFieldRange.apply_symm_apply]
  exact τ.restrictNormal_commutes j.fieldRange (j.equivFieldRange x)

end NormalEmbedding

section Composition

variable {A B C E F M : Type u} [Field A] [Field B] [Field C] [Field E] [Field F] [Field M]
    [Algebra A E] [Algebra B F] [Algebra C M]

/-- The continuous degree-two maps compose when the original Galois
pullbacks and field maps compose pointwise. -/
theorem galoisUnitsCohomologyMap_comp
    (r : Gal(F/B) →ₜ* Gal(E/A)) (s : Gal(M/C) →ₜ* Gal(F/B)) (t : Gal(M/C) →ₜ* Gal(E/A))
    (j : E →+* F) (i : F →+* M) (d : E →+* M)
    (hr : ∀ (σ : Gal(F/B)) (x : E), j (r σ x) = σ (j x))
    (hs : ∀ (σ : Gal(M/C)) (x : F), i (s σ x) = σ (i x))
    (ht : ∀ (σ : Gal(M/C)) (x : E), d (t σ x) = σ (d x))
    (hgroups : ∀ σ, r (s σ) = t σ) (hcoeff : ∀ x, i (j x) = d x) :
    ContinuousCohomology.map t (galoisUnitsMap t d ht) 2 =
      ContinuousCohomology.map r (galoisUnitsMap r j hr) 2 ≫
        ContinuousCohomology.map s (galoisUnitsMap s i hs) 2 := by
  have ht' : r.comp s = t := ContinuousMonoidHom.ext hgroups
  have hd : i.comp j = d := RingHom.ext hcoeff
  subst t
  subst d
  let α := galoisUnitsMap r j hr
  let β := galoisUnitsMap s i hs
  have h : galoisUnitsMap (r.comp s) (i.comp j) ht =
      (TopRep.resFunctor s.toMonoidHom).map α ≫ β := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  rw [h]
  exact ContinuousCohomology.map_comp r s α β 2

end Composition

variable {K L : Type u} [Field K] [Field L]
variable (f : K →+* L)
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))
variable (F : FiniteGaloisIntermediateField L (SeparableClosure L))
variable (hF : ∀ x : E, Field.absoluteGaloisGroup.separableClosureLift f (x : SeparableClosure K) ∈
  F.toIntermediateField)

private def stageUnitFieldMap : E →+* F :=
  ((Field.absoluteGaloisGroup.separableClosureLift f).comp E.toIntermediateField.val.toRingHom)
    |>.codRestrict F.toIntermediateField hF

private def absoluteToSourceStage : Gal(SeparableClosure L/L) →ₜ* Gal(E/K) :=
  (finiteGaloisRestriction E).comp (Field.absoluteGaloisGroup.separableMap f)

private theorem absoluteToSourceStage_commutes
    (σ : Gal(SeparableClosure L/L)) (x : E) :
    Field.absoluteGaloisGroup.separableClosureLift f (absoluteToSourceStage f E σ x) =
      σ (Field.absoluteGaloisGroup.separableClosureLift f (x : SeparableClosure K)) := by
  change Field.absoluteGaloisGroup.separableClosureLift f
      (finiteGaloisRestriction E (Field.absoluteGaloisGroup.separableMap f σ) x) = _
  rw [finiteGaloisRestriction_commutes]
  exact Field.absoluteGaloisGroup.separableMap_commutes f σ (x : SeparableClosure K)

private theorem finiteGaloisRestriction_surjective
    {M : Type u} [Field M] (T : FiniteGaloisIntermediateField M (SeparableClosure M)) :
    Function.Surjective (finiteGaloisRestriction T) :=
  AlgEquiv.restrictNormalHom_surjective (SeparableClosure M)

include hF in
private theorem stageRestriction_ker_le :
    (finiteGaloisRestriction F).toMonoidHom.ker ≤ (absoluteToSourceStage f E).toMonoidHom.ker := by
  intro σ hσ
  apply MonoidHom.mem_ker.mpr
  apply AlgEquiv.ext
  intro x
  apply E.toIntermediateField.val.injective
  apply (Field.absoluteGaloisGroup.separableClosureLift f).injective
  change Field.absoluteGaloisGroup.separableClosureLift f (absoluteToSourceStage f E σ x) =
    Field.absoluteGaloisGroup.separableClosureLift f (x : SeparableClosure K)
  rw [absoluteToSourceStage_commutes]
  have hfix := finiteGaloisRestriction_commutes F σ (stageUnitFieldMap f E F hF x)
  have hσone : finiteGaloisRestriction F σ = 1 := hσ
  rw [hσone, AlgEquiv.one_apply] at hfix
  exact hfix.symm

/-- The actual group pullback modulo the two defining finite stages. -/
def stageRestriction : Gal(F/L) →ₜ* Gal(E/K) where
  toMonoidHom := (finiteGaloisRestriction F).toMonoidHom.liftOfSurjective
    (finiteGaloisRestriction_surjective F)
    ⟨(absoluteToSourceStage f E).toMonoidHom, stageRestriction_ker_le f E F hF⟩
  continuous_toFun := continuous_of_discreteTopology

/-- Pullback at a finite stage commutes with the absolute restrictions. -/
theorem stageRestriction_comp_finiteGaloisRestriction (σ : Gal(SeparableClosure L/L)) :
    stageRestriction f E F hF (finiteGaloisRestriction F σ) =
      finiteGaloisRestriction E (Field.absoluteGaloisGroup.separableMap f σ) :=
  MonoidHom.liftOfRightInverse_comp_apply
    (f := (finiteGaloisRestriction F).toMonoidHom)
    (f_inv := Function.surjInv (finiteGaloisRestriction_surjective F))
    (Function.rightInverse_surjInv (finiteGaloisRestriction_surjective F))
    ⟨(absoluteToSourceStage f E).toMonoidHom, stageRestriction_ker_le f E F hF⟩ σ

private theorem stageRestriction_commutes (σ : Gal(F/L)) (x : E) :
    stageUnitFieldMap f E F hF (stageRestriction f E F hF σ x) =
      σ (stageUnitFieldMap f E F hF x) := by
  obtain ⟨τ, rfl⟩ := finiteGaloisRestriction_surjective F σ
  apply F.toIntermediateField.val.injective
  rw [stageRestriction_comp_finiteGaloisRestriction]
  exact (absoluteToSourceStage_commutes f E τ x).trans
    (finiteGaloisRestriction_commutes F τ (stageUnitFieldMap f E F hF x)).symm

private def stageCoefficientRestriction :
    TopRep.res (stageRestriction f E F hF).toMonoidHom (galoisUnitsRep K E) ⟶ galoisUnitsRep L F :=
  galoisUnitsMap (stageRestriction f E F hF) (stageUnitFieldMap f E F hF)
    (stageRestriction_commutes f E F hF)

/-- Restrict the finite-stage cochain using the original group and unit maps. -/
def relativeRestriction : relativeBr E →+ relativeBr F :=
  (ContinuousCohomology.map (stageRestriction f E F hF)
    (stageCoefficientRestriction f E F hF) 2).hom.toLinearMap.toAddMonoidHom

/-- Inflating a finite-stage restriction gives the actual absolute restriction. -/
theorem finiteInflation_relativeRestriction (x : relativeBr E) :
    finiteInflation F (relativeRestriction f E F hF x) = restrict f (finiteInflation E x) := by
  let j := Field.absoluteGaloisGroup.separableClosureLift f
  let q := Field.absoluteGaloisGroup.separableMap f
  let d := j.comp E.toIntermediateField.val.toRingHom
  let ψ := galoisUnitsMap q j (Field.absoluteGaloisGroup.separableMap_commutes f)
  have hl := galoisUnitsCohomologyMap_comp
    (stageRestriction f E F hF) (finiteGaloisRestriction F) (absoluteToSourceStage f E)
    (stageUnitFieldMap f E F hF) F.toIntermediateField.val.toRingHom d
    (stageRestriction_commutes f E F hF) (finiteGaloisRestriction_commutes F)
    (absoluteToSourceStage_commutes f E)
    (stageRestriction_comp_finiteGaloisRestriction f E F hF) (fun _ => rfl)
  have hr := galoisUnitsCohomologyMap_comp
    (finiteGaloisRestriction E) q (absoluteToSourceStage f E)
    E.toIntermediateField.val.toRingHom j d (finiteGaloisRestriction_commutes E)
    (Field.absoluteGaloisGroup.separableMap_commutes f) (absoluteToSourceStage_commutes f E)
    (fun _ => rfl) (fun _ => rfl)
  change ContinuousCohomology.map (finiteGaloisRestriction F) (finiteInflationCoefficientMap F) 2
      (ContinuousCohomology.map (stageRestriction f E F hF) (stageCoefficientRestriction f E F hF) 2
        x) =
    ContinuousCohomology.map q ψ 2
      (ContinuousCohomology.map (finiteGaloisRestriction E) (finiteInflationCoefficientMap E) 2 x)
  exact ConcreteCategory.congr_hom (hl.symm.trans hr) x

section EmbeddedStage

variable {A M : Type u} [Field A] [Field M] [Algebra A M]

/-- Restricting an inflated class factors through any specified compatible completed stage. -/
theorem restrictOfEmbedding_finiteInflation_eq_of_factor
    (q : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (jΩ : SeparableClosure K →+* SeparableClosure L)
    (hq : ∀ (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K), jΩ (q σ x) = σ (jΩ x))
    (r : Gal(M/A) →ₜ* Gal(E/K)) (j : E →+* M)
    (hr : ∀ (σ : Gal(M/A)) (x : E), j (r σ x) = σ (j x))
    (s : Gal(SeparableClosure L/L) →ₜ* Gal(M/A)) (i : M →+* SeparableClosure L)
    (hs : ∀ (σ : Gal(SeparableClosure L/L)) (x : M), i (s σ x) = σ (i x))
    (hgroups : ∀ σ : Gal(SeparableClosure L/L),
      r (s σ) = finiteGaloisRestriction E (q σ))
    (hcoeff : ∀ x : E, i (j x) = jΩ x)
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) 2) :
    restrictOfEmbedding q jΩ hq
      (finiteInflation E (ContinuousCohomology.π (galoisUnitsRep K E) 2 z)) =
      (ContinuousCohomology.map s (galoisUnitsMap s i hs) 2)
        (ContinuousCohomology.π (galoisUnitsRep A M) 2
          (ContinuousCohomology.cocyclesMap r (galoisUnitsMap r j hr) 2 z)) := by
  let t := (finiteGaloisRestriction E).comp q
  let d := jΩ.comp E.toIntermediateField.val.toRingHom
  have ht (σ : Gal(SeparableClosure L/L)) (x : E) : d (t σ x) = σ (d x) :=
    (congrArg jΩ (finiteGaloisRestriction_commutes E (q σ) x)).trans (hq σ x)
  have hleft := galoisUnitsCohomologyMap_comp (finiteGaloisRestriction E) q t
    E.toIntermediateField.val.toRingHom jΩ d (finiteGaloisRestriction_commutes E) hq ht
    (fun _ => rfl) (fun _ => rfl)
  have hright := galoisUnitsCohomologyMap_comp r s t j i d hr hs ht hgroups hcoeff
  have h₁ := ConcreteCategory.congr_hom (hleft.symm.trans hright) (π (galoisUnitsRep K E) 2 z)
  have h₂ : ContinuousCohomology.map r (galoisUnitsMap r j hr) 2 (π (galoisUnitsRep K E) 2 z) =
      π (galoisUnitsRep A M) 2 (cocyclesMap r (galoisUnitsMap r j hr) 2 z) :=
    ConcreteCategory.congr_hom (π_map r (galoisUnitsMap r j hr) 2) z
  simp only [ConcreteCategory.comp_apply, h₂] at h₁
  exact h₁

/-- The canonical restriction factors through the same actual completed stage. -/
theorem restrict_finiteInflation_eq_of_factor
    (r : Gal(M/A) →ₜ* Gal(E/K)) (j : E →+* M)
    (hr : ∀ (σ : Gal(M/A)) (x : E), j (r σ x) = σ (j x))
    (s : Gal(SeparableClosure L/L) →ₜ* Gal(M/A)) (i : M →+* SeparableClosure L)
    (hs : ∀ (σ : Gal(SeparableClosure L/L)) (x : M), i (s σ x) = σ (i x))
    (hgroups : ∀ σ : Gal(SeparableClosure L/L),
      r (s σ) = finiteGaloisRestriction E (Field.absoluteGaloisGroup.separableMap f σ))
    (hcoeff : ∀ x : E, i (j x) = Field.absoluteGaloisGroup.separableClosureLift f x)
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) 2) :
    restrict f (finiteInflation E (ContinuousCohomology.π (galoisUnitsRep K E) 2 z)) =
      (ContinuousCohomology.map s (galoisUnitsMap s i hs) 2)
        (ContinuousCohomology.π (galoisUnitsRep A M) 2
          (ContinuousCohomology.cocyclesMap r (galoisUnitsMap r j hr) 2 z)) :=
  restrictOfEmbedding_finiteInflation_eq_of_factor E (Field.absoluteGaloisGroup.separableMap f)
    (Field.absoluteGaloisGroup.separableClosureLift f)
    (Field.absoluteGaloisGroup.separableMap_commutes f)
    r j hr s i hs hgroups hcoeff z

end EmbeddedStage

section ConjugateEmbedding

variable {A M E₀ : Type u} [Field A] [Field M] [Field E₀]
    [Algebra A M] [Algebra K E₀] [LocallyCompactSpace Gal(E₀/K)]

/-- Composing the field embedding with a source automorphism does
not change pullback of the original degree-two classes. -/
theorem relativeCohomologyMap_comp_aut
    (τ : Gal(E₀/K)) (j : E₀ →+* M)
    (r₀ r : Gal(M/A) →ₜ* Gal(E₀/K))
    (h₀ : ∀ (σ : Gal(M/A)) (x : E₀), j (r₀ σ x) = σ (j x))
    (h : ∀ (σ : Gal(M/A)) (x : E₀),
      (j.comp τ.toRingHom) (r σ x) = σ ((j.comp τ.toRingHom) x)) :
    ContinuousCohomology.map r (galoisUnitsMap r (j.comp τ.toRingHom) h) 2 =
      ContinuousCohomology.map r₀ (galoisUnitsMap r₀ j h₀) 2 := by
  let c : Gal(E₀/K) →ₜ* Gal(E₀/K) :=
    { toFun := fun σ => τ⁻¹ * σ * τ
      map_one' := by group
      map_mul' := fun σ ρ => by group
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const }
  have hconj (σ : Gal(E₀/K)) : τ * c σ = σ * τ := by
    change τ * (τ⁻¹ * σ * τ) = σ * τ
    group
  have hc (σ : Gal(E₀/K)) (x : E₀) : τ (c σ x) = σ (τ x) :=
    congrArg (fun a : Gal(E₀/K) => a x) (hconj σ)
  have hgroups (σ : Gal(M/A)) : r σ = c (r₀ σ) := by
    apply AlgEquiv.ext
    intro x
    apply τ.injective
    apply j.injective
    change (j.comp τ.toRingHom) (r σ x) = j (τ (c (r₀ σ) x))
    rw [h, hc, h₀]
    rfl
  let γ := galoisUnitsMap c τ.toRingHom hc
  let φ := galoisUnitsMap r (j.comp τ.toRingHom) h
  let φ₀ := galoisUnitsMap r₀ j h₀
  have hγ (x : galoisUnitsRep K E₀) : γ x = (galoisUnitsRep K E₀).ρ τ x := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  have hid := ContinuousCohomology.map_inner_eq_id_two (galoisUnitsRep K E₀) τ c γ (fun _ => rfl) hγ
  have hcomp : ContinuousCohomology.map r φ 2 =
      ContinuousCohomology.map c γ 2 ≫ ContinuousCohomology.map r₀ φ₀ 2 :=
    galoisUnitsCohomologyMap_comp c r₀ r τ.toRingHom j (j.comp τ.toRingHom)
      hc h₀ h (fun σ => (hgroups σ).symm) (fun _ => rfl)
  exact hcomp.trans (by rw [hid, Category.id_comp])

end ConjugateEmbedding

end ClassFieldTheory.Brauer
