/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.Tactic.Simps.Basic

/-!
# Tor exact sequences for modules

Tensor a projective resolution with a short exact sequence, then transport its homology
sequence to Tor. Flat-module vanishing and the natural identification of Tor in degree
zero with the tensor product are shared by the local flatness and regular-sequence proofs.
-/

namespace AlgebraicCurves.Foundations.Algebra.TorExactSequence

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

section TorLES
variable {R : Type u} [CommRing R]

theorem torLES_tensorRight_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (M : ModuleCat.{u} R) [Module.Flat R M] :
    (S.map (tensorRight M)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight M))
    (hS.map_of_exact (tensorLeft M))
/-- Tensor a short complex with each term of the chosen projective resolution. -/
@[reducible, simps]
noncomputable def torLES_resolutionTensorSES (S : ShortComplex (ModuleCat.{u} R))
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
    (by
      ext i : 1
      change S.f ▷ (P.complex.X i) ≫ S.g ▷ (P.complex.X i) = 0
      rw [← comp_whiskerRight, S.zero, MonoidalPreadditive.zero_whiskerRight])

theorem torLES_resolutionTensorSES_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) :
    (torLES_resolutionTensorSES S P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact torLES_tensorRight_shortExact hS (P.complex.X i)

variable {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y)

/-- Identify Tor with the homology of the tensor product with the chosen resolution. -/
noncomputable def torLES_torIso (X : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).obj X).obj Y ≅
      ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology n :=
  P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) n

theorem torLES_torMap_app_eq {X X' : ModuleCat.{u} R} (f : X ⟶ X') (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).map f).app Y =
      (torLES_torIso P X n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) n ≫
        (torLES_torIso P X' n).inv :=
  P.leftDerived_app_eq ((curriedTensor (ModuleCat.{u} R)).map f) n

/-- The connecting map in the Tor long exact sequence, computed using the chosen resolution. -/
noncomputable def torLES_torDelta (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj Y ⟶
      ((Tor (ModuleCat.{u} R) n).obj S.X₁).obj Y :=
  (torLES_torIso P S.X₃ (n + 1)).hom ≫
    (torLES_resolutionTensorSES_shortExact S hS P).δ (n + 1) n (by rfl) ≫
    (torLES_torIso P S.X₁ n).inv
include P in
theorem torLES_torMap_comp_eq_zero (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).map S.f).app Y ≫
      ((Tor (ModuleCat.{u} R) n).map S.g).app Y = 0 := by
  have hz : HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).f n ≫
      HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).g n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, (torLES_resolutionTensorSES S P).zero,
      HomologicalComplex.homologyMap_zero]
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  rw [torLES_torMap_app_eq P S.f n, torLES_torMap_app_eq P S.g n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp only [comp_zero, zero_comp]

theorem torLES_torMap_comp_torDelta_eq_zero (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) (n + 1)).map S.g).app Y ≫ torLES_torDelta P S hS n = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).comp_δ (n + 1) n (by rfl)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq P S.g (n + 1)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp only [comp_zero, zero_comp]

theorem torLES_torDelta_comp_eq_zero (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    torLES_torDelta P S hS n ≫ ((Tor (ModuleCat.{u} R) n).map S.f).app Y = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).δ_comp (n + 1) n (by rfl)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq P S.f n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp only [comp_zero, zero_comp]

theorem torLES_tor_exact₂ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{u} R) n).map S.f).app Y)
      (((Tor (ModuleCat.{u} R) n).map S.g).app Y)
      (torLES_torMap_comp_eq_zero P S n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₁ n).symm (torLES_torIso P S.X₂ n).symm
      (torLES_torIso P S.X₃ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₂ n)
  · exact (Iso.inv_comp_eq (torLES_torIso P S.X₁ n)).mpr
      (torLES_torMap_app_eq P S.f n)
  · exact (Iso.inv_comp_eq (torLES_torIso P S.X₂ n)).mpr
      (torLES_torMap_app_eq P S.g n)

theorem torLES_tor_exact₃ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{u} R) (n + 1)).map S.g).app Y)
      (torLES_torDelta P S hS n)
      (torLES_torMap_comp_torDelta_eq_zero P S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₂ (n + 1)).symm
      (torLES_torIso P S.X₃ (n + 1)).symm (torLES_torIso P S.X₁ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₃ (n + 1) n (by rfl))
  · exact (Iso.inv_comp_eq (torLES_torIso P S.X₂ (n + 1))).mpr
      (torLES_torMap_app_eq P S.g (n + 1))
  · exact (Iso.inv_comp_eq (torLES_torIso P S.X₃ (n + 1))).mpr rfl

theorem torLES_tor_exact₁ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (torLES_torDelta P S hS n)
      (((Tor (ModuleCat.{u} R) n).map S.f).app Y)
      (torLES_torDelta_comp_eq_zero P S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₃ (n + 1)).symm
      (torLES_torIso P S.X₁ n).symm (torLES_torIso P S.X₂ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₁ (n + 1) n (by rfl))
  · exact (Iso.inv_comp_eq (torLES_torIso P S.X₃ (n + 1))).mpr rfl
  · exact (Iso.inv_comp_eq (torLES_torIso P S.X₁ n)).mpr
      (torLES_torMap_app_eq P S.f n)
include P in
theorem torLES_tor_isZero_X₂ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) (h₁ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₁).obj Y))
    (h₃ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj Y)) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₂).obj Y) :=
  (torLES_tor_exact₂ P S hS (n + 1)).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end TorLES

section TorFV
variable {R : Type u} [CommRing R]

theorem torFV_resolutionTensor_exactAt (M : ModuleCat.{u} R) [Module.Flat R M]
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) (n : ℕ) :
    ((((curriedTensor (ModuleCat.{u} R)).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).ExactAt (n + 1) :=
  Module.Flat.lTensor_shortComplex_exact M (P.complex.sc (n + 1))
    (P.complex_exactAt_succ n)

theorem torFV_tor_succ_isZero_of_flat_res (M : ModuleCat.{u} R) [Module.Flat R M]
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj Y) := by
  refine IsZero.of_iso ?_ (torLES_torIso P M (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact torFV_resolutionTensor_exactAt M P n

theorem torFV_tor_succ_isZero_of_flat (M : ModuleCat.{u} R) [Module.Flat R M]
    (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  exact torFV_tor_succ_isZero_of_flat_res M P n

theorem torFV_tor_one_isZero_of_flat (M : ModuleCat.{u} R) [Module.Flat R M]
    (Y : ModuleCat.{u} R) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj Y) :=
  torFV_tor_succ_isZero_of_flat M Y 0

theorem torFV_tor_succ_isZero_of_isZero (X : ModuleCat.{u} R) (hX : IsZero X)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj X).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  refine IsZero.of_iso ?_ (torLES_torIso P X (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.ExactAt.of_isZero
    ((tensorRight (P.complex.X (n + 1))).map_isZero hX)

theorem torFV_tor_one_isZero_of_isZero (X : ModuleCat.{u} R) (hX : IsZero X)
    (Y : ModuleCat.{u} R) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj X).obj Y) :=
  torFV_tor_succ_isZero_of_isZero X hX Y 0

end TorFV

section TorZeroBridge
variable {R : Type u} [CommRing R]

theorem ar_opcyclesMap_fromLeftDerivedZero'_naturality
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{u} R}
    (f : X ⟶ X') :
    HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X') =
      P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X) ≫
        ((curriedTensor (ModuleCat.{u} R)).map f).app Y := by
  rw [← cancel_epi (HomologicalComplex.pOpcycles
    ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex) 0)]
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero', ← Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  exact (((curriedTensor (ModuleCat.{u} R)).map f).naturality (P.π.f 0)).symm

theorem ar_tor0_map_fromLeftDerivedZero_naturality
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{u} R}
    (f : X ⟶ X') :
    ((Tor (ModuleCat.{u} R) 0).map f).app Y ≫
        ((curriedTensor (ModuleCat.{u} R)).obj X').fromLeftDerivedZero.app Y =
      ((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y ≫
        ((curriedTensor (ModuleCat.{u} R)).map f).app Y := by
  have hM : ((Tor (ModuleCat.{u} R) 0).map f).app Y =
      (torLES_torIso P X 0).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 ≫
        (torLES_torIso P X' 0).inv :=
    torLES_torMap_app_eq P f 0
  have hF : ((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X) :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{u} R)).obj X)
  have hG : ((curriedTensor (ModuleCat.{u} R)).obj X').fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X') 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X') :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{u} R)).obj X')
  have hι : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 =
      HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 := by
    apply HomologicalComplex.homologyι_naturality
  have hO := ar_opcyclesMap_fromLeftDerivedZero'_naturality P f
  have hbr : ∀ {Z : ModuleCat.{u} R}
      (h : ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 0 ⟶ Z),
      (torLES_torIso P X' 0).inv ≫
        (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X') 0).hom ≫ h = h :=
    fun {Z} h => (torLES_torIso P X' 0).inv_hom_id_assoc h
  have hbr2 : (torLES_torIso P X 0).hom =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom := rfl
  rw [hM, hF, hG]
  simp only [Category.assoc]
  refine Eq.trans (whisker_eq (torLES_torIso P X 0).hom
    (whisker_eq (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
        (ComplexShape.down ℕ)).app P.complex) 0)
      (hbr (HomologicalComplex.homologyι
        ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X'))))) ?_
  refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hι _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hO)) ?_
  exact eq_whisker hbr2 _

end TorZeroBridge

end

end AlgebraicCurves.Foundations.Algebra.TorExactSequence
