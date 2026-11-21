/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.DirectSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

/-! # Finite-support idele gluing for cohomological Brauer localization -/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField GlobalClassFieldTheory.Reciprocity
open scoped BigOperators IsMulCommutative NumberField

namespace ClassFieldTheory.Brauer

universe u v

variable (K : Type u) [Field K] [NumberField K]

/-- Project an ordinary idele to the unit group of the indicated completion. -/
def placeIdeleComponent (w : Place K) : IdeleGroup K →* (placeCompletion K w)ˣ := by
  cases w with
  | inl w => exact IdeleGroup.finiteComponent w
  | inr w => exact IdeleGroup.infiniteComponent w

/-- Insert a unit of an original completion as a one-place ordinary idele. -/
def onePlaceIdele (w : Place K) : (placeCompletion K w)ˣ →* IdeleGroup K := by
  cases w with
  | inl w => exact IdeleGroup.finitePlaceIdele w
  | inr w => exact IdeleGroup.infinitePlaceIdele w

@[simp]
theorem placeIdeleComponent_onePlaceIdele_same (w : Place K) (a : (placeCompletion K w)ˣ) :
    placeIdeleComponent K w (onePlaceIdele K w a) = a := by
  cases w with
  | inl w => exact IdeleGroup.finitePlaceIdele_finiteComponent_same w a
  | inr w => exact IdeleGroup.infinitePlaceIdele_infiniteComponent_same w a

theorem placeIdeleComponent_onePlaceIdele_of_ne (w z : Place K) (a : (placeCompletion K z)ˣ)
    (h : w ≠ z) : placeIdeleComponent K w (onePlaceIdele K z a) = 1 := by
  cases w with
  | inl w =>
    cases z with
    | inl z =>
      exact IdeleGroup.finitePlaceIdele_finiteComponent_of_ne z w a
        (fun he => h (congrArg Sum.inl he))
    | inr z => exact IdeleGroup.infinitePlaceIdele_finiteComponent z w a
  | inr w =>
    cases z with
    | inl z => exact IdeleGroup.finitePlaceIdele_infiniteComponent z w a
    | inr z =>
      exact IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne z w a
        (fun he => h (congrArg Sum.inr he))

/-- The ordinary idele having given components on a finite set and one elsewhere. -/
def supportedLocalUnitIdele (S : Finset (Place K)) (a : ∀ w, (placeCompletion K w)ˣ) :
    IdeleGroup K :=
  ∏ w ∈ S, onePlaceIdele K w (a w)

open scoped Classical in
theorem placeIdeleComponent_supportedLocalUnitIdele (S : Finset (Place K))
    (a : ∀ w, (placeCompletion K w)ˣ) (w : Place K) :
    placeIdeleComponent K w (supportedLocalUnitIdele K S a) = if w ∈ S then a w else 1 := by
  classical
  unfold supportedLocalUnitIdele
  rw [map_prod]
  by_cases hw : w ∈ S
  · rw [ite_eq_left hw, Finset.prod_eq_single_of_mem w hw]
    · exact placeIdeleComponent_onePlaceIdele_same K w (a w)
    · intro z _ hz
      exact placeIdeleComponent_onePlaceIdele_of_ne K w z (a z) hz.symm
  · rw [ite_eq_right hw]
    refine Finset.prod_eq_one fun z hz => ?_
    exact placeIdeleComponent_onePlaceIdele_of_ne K w z (a z) (fun h => hw (h ▸ hz))

section Artin

variable (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]

/-- Arithmetic local reciprocity in the Galois group of the original global extension. -/
def placeUnitArtin (w : Place K) : (placeCompletion K w)ˣ →* Gal(L/K) := by
  cases w with
  | inl w => exact arithmeticChosenFinitePlaceArtinMonoidHom K L w
  | inr w => exact arithmeticChosenInfinitePlaceArtinMonoidHom K L w

@[simp]
theorem arithmeticGlobalArtin_onePlaceIdele (w : Place K) (a : (placeCompletion K w)ˣ) :
    arithmeticGlobalArtinMonoidHom K L (onePlaceIdele K w a) = placeUnitArtin K L w a := by
  cases w with
  | inl w => exact arithmeticGlobalArtinMonoidHom_finitePlaceIdele K L w a
  | inr w => exact arithmeticGlobalArtinMonoidHom_infinitePlaceIdele K L w a

/-- Arithmetic reciprocity on a supported idele is the product of its prescribed local values. -/
theorem arithmeticGlobalArtin_supportedLocalUnitIdele (S : Finset (Place K))
    (a : ∀ w, (placeCompletion K w)ˣ) :
    arithmeticGlobalArtinMonoidHom K L (supportedLocalUnitIdele K S a) =
      ∏ w ∈ S, placeUnitArtin K L w (a w) := by
  unfold supportedLocalUnitIdele
  rw [map_prod]
  exact Finset.prod_congr rfl (fun w _ => arithmeticGlobalArtin_onePlaceIdele K L w (a w))

/-- The global arithmetic symbol is the product over any finite set containing
all the nontrivial one-place symbols of the ordinary idele. -/
theorem arithmeticGlobalArtin_eq_prod_placeUnitArtin (a : IdeleGroup K) (S : Finset (Place K))
    (h : ∀ w, w ∉ S → placeUnitArtin K L w (placeIdeleComponent K w a) = 1) :
    arithmeticGlobalArtinMonoidHom K L a =
      ∏ w ∈ S, placeUnitArtin K L w (placeIdeleComponent K w a) := by
  classical
  let f (v : HeightOneSpectrum (𝓞 K)) :=
    chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v (IdeleGroup.finiteComponent v a)
  let g (v : InfinitePlace K) :=
    chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v (IdeleGroup.infiniteComponent v a)
  have hf : Function.mulSupport f ⊆ S.toLeft := by
    intro v hv
    by_contra hn
    apply hv
    have hh := h (Sum.inl v) (fun hm => hn (Finset.mem_toLeft.mpr hm))
    simpa only [placeUnitArtin, placeIdeleComponent,
      arithmeticChosenFinitePlaceArtinMonoidHom_apply, inv_eq_one] using hh
  have hg : (∏ w ∈ S.toRight, g w) = ∏ w, g w := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro w _ hw
    have hh := h (Sum.inr w) (fun hm => hw (Finset.mem_toRight.mpr hm))
    simpa only [placeUnitArtin, placeIdeleComponent,
      arithmeticChosenInfinitePlaceArtinMonoidHom_apply, inv_eq_one] using hh
  rw [arithmeticGlobalArtinMonoidHom_apply, globalArtinMonoidHom_apply]
  change ((∏ w, g w) * ∏ᶠ v, f v)⁻¹ = _
  rw [finprod_eq_prod_of_mulSupport_subset f hf, ← hg, mul_inv_rev,
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  have hinv (s : Finset (HeightOneSpectrum (𝓞 K))) :
      (∏ v ∈ s, f v)⁻¹ = ∏ v ∈ s, (f v)⁻¹ :=
    map_prod (MulEquiv.inv (Gal(L/K))).toMonoidHom f s
  have hinv' (s : Finset (InfinitePlace K)) :
      (∏ v ∈ s, g v)⁻¹ = ∏ v ∈ s, (g v)⁻¹ :=
    map_prod (MulEquiv.inv (Gal(L/K))).toMonoidHom g s
  rw [hinv, hinv']
  simp only [f, g, placeUnitArtin, placeIdeleComponent,
    arithmeticChosenFinitePlaceArtinMonoidHom_apply,
    arithmeticChosenInfinitePlaceArtinMonoidHom_apply]

/-- The component of any ordinary idele norm is killed by the local Artin map. -/
theorem placeUnitArtin_component_norm (a : IdeleGroup L) (w : Place K) :
    placeUnitArtin K L w (placeIdeleComponent K w (IdeleGroup.norm K L a)) = 1 := by
  let b := (relativeIdeleBaseChangeMulEquiv (K := K) (L := L)).symm a
  have hb : IdeleGroup.norm K L a = RelativeIdeleGroup.norm K L b := by
    rw [← IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, MulEquiv.apply_symm_apply]
  rw [hb]
  cases w with
  | inl w =>
    change arithmeticChosenFinitePlaceArtinMonoidHom K L w
      (IdeleGroup.finiteComponent w (RelativeIdeleGroup.norm K L b)) = 1
    rw [arithmeticChosenFinitePlaceArtinMonoidHom_apply, inv_eq_one,
      chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm]
    exact relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup (K := K) (L := L) w b
  | inr w =>
    change arithmeticChosenInfinitePlaceArtinMonoidHom K L w
      (IdeleGroup.infiniteComponent w (RelativeIdeleGroup.norm K L b)) = 1
    rw [arithmeticChosenInfinitePlaceArtinMonoidHom_apply, inv_eq_one,
      chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm]
    exact infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
      (K := K) (L := L) (RelativeIdeleGroup.norm K L b) ⟨b, rfl⟩ w

/-- An idele killed by arithmetic global Artin is a principal idele times an ordinary norm. -/
theorem exists_principalIdele_mul_norm_of_arithmeticGlobalArtin_eq_one (a : IdeleGroup K)
    (ha : arithmeticGlobalArtinMonoidHom K L a = 1) :
    ∃ (x : Kˣ) (b : IdeleGroup L), a = IdeleGroup.principalIdele K x * IdeleGroup.norm K L b := by
  let qK := IdeleGroup.toStandardClass K
  have h : qK a ∈ (ideleClassNorm K L).range := by
    rw [← arithmeticGlobalNormResidueMonoidHom_ker]
    apply MonoidHom.mem_ker.mpr
    exact (DFunLike.congr_fun
      (arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin K L) a).trans ha
  obtain ⟨c, hc⟩ := h
  obtain ⟨b, rfl⟩ := IdeleGroup.toStandardClass_surjective L c
  have hh : qK (IdeleGroup.norm K L b) = qK a := (ideleClassNorm_mk K L b).symm.trans hc
  have hdiv : a / IdeleGroup.norm K L b ∈ (IdeleGroup.principalIdele K).range := by
    rw [div_eq_mul_inv, mul_comm]
    exact (IdeleGroup.toStandardClass_eq_iff K (IdeleGroup.norm K L b) a).mp hh
  obtain ⟨x, hx⟩ := hdiv
  exact ⟨x, b, by rw [hx, div_mul_cancel]⟩

/-- If an idele has global symbol one, a single base unit realizes all its local Artin symbols. -/
theorem exists_principalUnit_of_arithmeticGlobalArtin_eq_one (a : IdeleGroup K)
    (ha : arithmeticGlobalArtinMonoidHom K L a = 1) :
    ∃ x : Kˣ, ∀ w : Place K,
      placeUnitArtin K L w (placeIdeleComponent K w (IdeleGroup.principalIdele K x)) =
        placeUnitArtin K L w (placeIdeleComponent K w a) := by
  obtain ⟨x, b, rfl⟩ := exists_principalIdele_mul_norm_of_arithmeticGlobalArtin_eq_one K L a ha
  exact ⟨x, fun w => by rw [map_mul, map_mul, placeUnitArtin_component_norm, mul_one]⟩

end Artin

end ClassFieldTheory.Brauer
