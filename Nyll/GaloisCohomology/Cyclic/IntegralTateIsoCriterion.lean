/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Nyll.GaloisCohomology.Cyclic.IntegralTatePSubgroups

/-!
# An all-degree isomorphism criterion for an original coefficient map

Adjoining the coinduced unit embeds the source of a coefficient morphism
into a biproduct with the target. The original Tate sequence reduces the
criterion to two consecutive vanishings for the cokernel on the
prime-power subgroups.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

attribute [local instance] tateFiniteSubgroup

private theorem projection_tate_bijective {A B C : Rep.{u} ℤ G}
    (p : B ⟶ A) (i : A ⟶ B) (q : B ⟶ C) (j : C ⟶ B) (n : ℤ)
    (hpi : i ≫ p = 𝟙 A) (h : p ≫ i + q ≫ j = 𝟙 B) (hz : IsZero (tate C n)) :
    Function.Bijective ((tateFunctor G n).map p) := by
  let F := tateFunctor G n
  have hq : F.map q = 0 := hz.eq_of_tgt _ _
  have h₁ : F.map p ≫ F.map i = 𝟙 (tate B n) := by
    have e : F.map (p ≫ i + q ≫ j) = F.map (𝟙 B) := congrArg F.map h
    rw [F.map_add, F.map_comp, F.map_comp, hq, zero_comp, add_zero] at e
    exact e.trans (F.map_id B)
  have h₂ : F.map i ≫ F.map p = 𝟙 (tate A n) :=
    (F.map_comp i p).symm.trans ((congrArg F.map hpi).trans (F.map_id A))
  let e : tate B n ≅ tate A n := ⟨F.map p, F.map i, h₁, h₂⟩
  exact e.toLinearEquiv.bijective

private theorem cokernel_tate_isZero_of_surj_inj {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (n : ℤ) (hs : Function.Surjective ((tateFunctor G n).map S.f))
    (hi : Function.Injective ((tateFunctor G (n + 1)).map S.f)) : IsZero (tate S.X₃ n) := by
  have hz (x : tate S.X₃ n) : x = 0 := by
    have hδ : tateδ hS n x = 0 := hi ((tate_map_f_δ_eq_zero hS n x).trans (map_zero _).symm)
    obtain ⟨y, rfl⟩ := exists_tate_preimage_of_δ_eq_zero hS n x hδ
    obtain ⟨z, rfl⟩ := hs y
    change ((tateFunctor G n).map S.f ≫ (tateFunctor G n).map S.g) z = 0
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
    rfl
  have : Subsingleton (tate S.X₃ n) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

private theorem tateMap_degree_inv_apply {A B : Rep.{u} ℤ G} (f : A ⟶ B) {i j : ℤ}
    (h : i = j) (x : tate A j) :
    (tateFunctor G i).map f ((eqToIso (congrArg (tate A) h)).inv x) =
      (eqToIso (congrArg (tate B) h)).inv ((tateFunctor G j).map f x) := by
  subst j
  rfl

private theorem tateMap_bijective_of_cokernel_isZero {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (n : ℤ) (hprev : IsZero (tate S.X₃ (n - 1))) (hn : IsZero (tate S.X₃ n)) :
    Function.Bijective ((tateFunctor G n).map S.f) := by
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    have hn' : n - 1 + 1 = n := sub_add_cancel n 1
    let y : tate S.X₁ (n - 1 + 1) := (eqToIso (congrArg (tate S.X₁) hn')).inv x
    have hy : (tateFunctor G (n - 1 + 1)).map S.f y = 0 := by
      change (tateFunctor G (n - 1 + 1)).map S.f ((eqToIso (congrArg (tate S.X₁) hn')).inv x) = 0
      rw [tateMap_degree_inv_apply S.f hn' x, hx, map_zero]
    obtain ⟨z, hz⟩ := exists_tate_δ_preimage_of_map_eq_zero hS (n - 1) y hy
    have : Subsingleton (tate S.X₃ (n - 1)) := ModuleCat.subsingleton_of_isZero hprev
    have hz₀ : z = 0 := Subsingleton.elim _ _
    have hzero : y = 0 := hz.symm.trans (by rw [hz₀, map_zero])
    exact ((eqToIso (congrArg (tate S.X₁) hn')).symm.toLinearEquiv.injective
      (hzero.trans (map_zero _).symm))
  · intro x
    have : Subsingleton (tate S.X₃ n) := ModuleCat.subsingleton_of_isZero hn
    exact exists_tate_preimage_of_map_g_eq_zero hS n x (Subsingleton.elim _ _)

/-- An original coefficient map which is surjective, bijective, and
injective in three consecutive Tate degrees on the prime-power subgroups
is bijective in every integer degree on the whole group. -/
theorem tateMap_bijective_of_pSubgroups {A B : Rep.{u} ℤ G} (f : A ⟶ B) (d : ℤ)
    (hs : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      Function.Surjective ((tateFunctor H (d - 1)).map ((Rep.resFunctor H.subtype).map f)))
    (hb : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      Function.Bijective ((tateFunctor H d).map ((Rep.resFunctor H.subtype).map f)))
    (hi : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      Function.Injective ((tateFunctor H (d + 1)).map ((Rep.resFunctor H.subtype).map f)))
    (n : ℤ) : Function.Bijective ((tateFunctor G n).map f) := by
  let C := (Rep.coindShiftSequence A).X₂
  let a : A ⟶ B ⊞ C := biprod.lift f (Rep.coindShiftUnit A)
  have haf : a ≫ biprod.fst = f := biprod.lift_fst f (Rep.coindShiftUnit A)
  have : Mono a := mono_of_mono_fac (biprod.lift_snd f (Rep.coindShiftUnit A))
  let S := ShortComplex.cokernelSequence a
  have hS : S.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact a
    mono_f := inferInstanceAs (Mono a)
    epi_g := inferInstanceAs (Epi (cokernel.π a)) }
  have hprojection (H : Subgroup G) (m : ℤ) :
      Function.Bijective ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map
        (biprod.fst : B ⊞ C ⟶ B))) := by
    let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
    apply projection_tate_bijective (F.map biprod.fst) (F.map biprod.inl)
      (F.map biprod.snd) (F.map biprod.inr) m
    · rw [← Functor.map_comp, biprod.inl_fst]
      exact F.map_id B
    · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, biprod.total]
      exact F.map_id (B ⊞ C)
    · exact tate_resCoindBot_isZero H (Rep.res (⊥ : Subgroup G).subtype A) m
  have hfactor (H : Subgroup G) (m : ℤ) (x : tate (Rep.res H.subtype A) m) :
      (tateFunctor H m).map ((Rep.resFunctor H.subtype).map biprod.fst)
          ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map a) x) =
        (tateFunctor H m).map ((Rep.resFunctor H.subtype).map f) x := by
    change (((tateFunctor H m).map ((Rep.resFunctor H.subtype).map a)) ≫
      ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map biprod.fst))) x = _
    rw [← Functor.map_comp, ← Functor.map_comp, haf]
  have hsurj (H : Subgroup G) (m : ℤ)
      (hm : Function.Surjective ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map f))) :
      Function.Surjective ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map a)) := by
    intro y
    obtain ⟨x, hx⟩ := hm ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map biprod.fst) y)
    exact ⟨x, (hprojection H m).injective ((hfactor H m x).trans hx)⟩
  have hinj (H : Subgroup G) (m : ℤ)
      (hm : Function.Injective ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map f))) :
      Function.Injective ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map a)) := by
    intro x y he
    apply hm
    rw [← hfactor H m x, ← hfactor H m y, he]
  have hz₁ : TateVanishingOnPSubgroups S.X₃ (d - 1) := by
    intro p _ H hH
    apply cokernel_tate_isZero_of_surj_inj (subgroupRestrict_shortExact H hS) (d - 1)
      (hsurj H (d - 1) (hs p H hH))
    change Function.Injective ((tateFunctor H (d - 1 + 1)).map ((Rep.resFunctor H.subtype).map a))
    rw [sub_add_cancel]
    exact hinj H d (hb p H hH).injective
  have hz₂ : TateVanishingOnPSubgroups S.X₃ (d - 1 + 1) := by
    rw [sub_add_cancel]
    intro p _ H hH
    exact cokernel_tate_isZero_of_surj_inj (subgroupRestrict_shortExact H hS) d
      (hsurj H d (hb p H hH).surjective) (hinj H (d + 1) (hi p H hH))
  have hZ (m : ℤ) : IsZero (tate S.X₃ m) :=
    tate_isZero_of_adjacent_pSubgroups S.X₃ (d - 1) m hz₁ hz₂
  have ha := tateMap_bijective_of_cokernel_isZero hS n (hZ (n - 1)) (hZ n)
  have hp := projection_tate_bijective (biprod.fst : B ⊞ C ⟶ B) biprod.inl biprod.snd biprod.inr n
    biprod.inl_fst biprod.total (coind_tate_isZero (Rep.res (⊥ : Subgroup G).subtype A) n)
  have hf : (tateFunctor G n).map f =
      (tateFunctor G n).map a ≫ (tateFunctor G n).map biprod.fst := by
    rw [← Functor.map_comp, haf]
  rw [hf]
  exact hp.comp ha

end IntegralGroupCohomology.Universe
