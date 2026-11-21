/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.RingTheory.TensorProduct.Maps
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Tactic.Choose

/-!
# Scheme exists alg Equiv tensor sections pullback fst preimage of is Affine Open
-/

@[expose] public section

section AffinePullbackSectionTensor

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (A : Type u) [CommRing A] [Algebra R A]

/-- The base change of the scheme along the given algebra map. -/
abbrev XA : Scheme.{u} := Limits.pullback c (specMap R A)

/-- The base-change projection to the original scheme. -/
abbrev fst : XA c A ⟶ X
  := Limits.pullback.fst c (specMap R A)

/-- The base-change projection to the spectrum of the new coefficient ring. -/
abbrev snd : XA c A ⟶
  Spec (.of A) := Limits.pullback.snd c (specMap R A)


variable (U : X.Opens) (hU : IsAffineOpen U)

theorem specMap_algebraMap_eq :
    letI := algebraOfHom c U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ c := by
  let := algebraOfHom c U
  have halg : (algebraMap R Γ(X, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom :=
    rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ←
    IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ c ⁻¹ᵁ
      ⊤)]

/-- The affine-open base change identified with the spectrum of the tensor product. -/
def pullbackAffineOpenIsoSpecTensor :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).toScheme ≅ Spec (.of (Γ(X, U) ⊗[R] A)) :=
  letI := algebraOfHom c U
  (pullbackRestrictIsoRestrict (fst c A) U).symm
    ≪≫ pullbackSymmetry _ _
    ≪≫ pullbackRightPullbackFstIso c (specMap R A) U.ι
    ≪≫ asIso (pullback.map (U.ι ≫ c) (specMap R A)
        (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) (specMap R A)
        hU.isoSpec.hom (𝟙 _) (𝟙 _)
        (by
          rw [Category.comp_id, specMap_algebraMap_eq c U hU,
            ← hU.isoSpec_inv_ι_assoc, Iso.hom_inv_id_assoc])
        (by rw [Category.id_comp, Category.comp_id]))
    ≪≫ pullbackSpecIso R Γ(X, U) A

/-- The ring equivalence between the tensor product and sections on the affine-open base change. -/
def sigma :
    letI := algebraOfHom c U
    (Γ(X, U) ⊗[R] A) ≃+* Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U
  ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).symm
    ≪≫ Scheme.Γ.mapIso (pullbackAffineOpenIsoSpecTensor c A U hU).op
    ≪≫ ((fst c A) ⁻¹ᵁ U).topIso).commRingCatIsoToRingEquiv

theorem sigma_apply (x : letI := algebraOfHom c U; Γ(X, U) ⊗[R] A) :
    letI := algebraOfHom c U
    sigma c A U hU x = ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).inv
      ≫ (pullbackAffineOpenIsoSpecTensor c A U hU).hom.appTop ≫ ((fst c A) ⁻¹ᵁ U).topIso.hom).hom x
        :=
  rfl

theorem iso_hom_comp_sndLeg :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).ι ≫ snd c A
      = (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R]
          A)) := by
  let := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_snd R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, pullbackRestrictIsoRestrict_inv_fst_assoc]

theorem iso_hom_comp_fstLeg :
    letI := algebraOfHom c U
    (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X,
          U) ⊗[R] A))
      = ((fst c A) ∣_ U) ≫ hU.isoSpec.hom := by
  let := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_fst R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc,
      pullbackSymmetry_hom_comp_fst_assoc]
  rfl

omit [CommRing R] in
theorem opens_ι_appTop_topIso_hom {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (Y.presheaf.map_comp _ _).symm.trans (congrArg Y.presheaf.map (Subsingleton.elim _ _))

omit [CommRing R] in
theorem topIso_morphismRestrict_appTop_topIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (W : Z.Opens) :
    W.topIso.inv ≫ (g ∣_ W).appTop ≫ (g ⁻¹ᵁ W).topIso.hom = g.app W := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict g (U := W)]
  apply (W.topIso.inv_comp_eq).mpr
  have h := (arrowResLEAppIso g W (g ⁻¹ᵁ W) le_rfl).hom.w.symm
  change (g.resLE W (g ⁻¹ᵁ W) le_rfl).appTop ≫ (g ⁻¹ᵁ W).topIso.hom =
    W.topIso.hom ≫ g.appLE W (g ⁻¹ᵁ W) le_rfl at h
  simpa only [Scheme.Hom.appLE_eq_app] using h


theorem sigma_tmul_one (s : Γ(X, U)) :
    letI := algebraOfHom c U
    sigma c A U hU (s ⊗ₜ[R] (1 : A)) = ((fst c A).app U).hom s := by
  let := algebraOfHom c U
  rw [sigma_apply]
  have hiL : s ⊗ₜ[R] (1 : A)
      = (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[R]
        A)).hom s := rfl
  rw [hiL, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality,
    Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    iso_hom_comp_fstLeg c A U hU, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  simp only [← Category.assoc]
  rw [hΓ, Category.id_comp, Category.assoc, topIso_morphismRestrict_appTop_topIso]

theorem sigma_one_tmul (a : A) :
    letI := algebraOfHom c U
    sigma c A U hU ((1 : Γ(X, U)) ⊗ₜ[R] a)
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  let := algebraOfHom c U
  rw [sigma_apply]
  have hiR : (1 : Γ(X, U)) ⊗ₜ[R] a
      = (CommRingCat.ofHom (R := A) (S := Γ(X, U) ⊗[R] A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R] A)).hom a := rfl
  rw [hiR, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality,
    Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    ← iso_hom_comp_sndLeg c A U hU, Scheme.Hom.comp_appTop, Category.assoc,
    opens_ι_appTop_topIso_hom ((fst c A) ⁻¹ᵁ U)]
  rfl

theorem algebraMap_sndAlgebra (a : A) :
    (algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)).algebraMap a
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  rw [algebraMap_algebraOfHom]
  rfl

/-- The algebra equivalence from the tensor product to sections on the affine-open base change. -/
def algEquiv :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    (A ⊗[R] Γ(X, U)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A Γ(X, U)).toRingEquiv.trans (sigma c A
    U hU))
    (fun a => by
      change sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) (algebraMap A (A ⊗[R] Γ(X,
        U)) a)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, show algebraMap A A a = a from rfl,
        Algebra.TensorProduct.comm_tmul, sigma_one_tmul, algebraMap_sndAlgebra])

theorem algEquiv_one_tmul (s : Γ(X, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    algEquiv c A U hU ((1 : A) ⊗ₜ[R] s) = ((fst c A).app U).hom s := by
  let := algebraOfHom c U; let := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  change sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) ((1 : A) ⊗ₜ[R] s)) = _
  rw [Algebra.TensorProduct.comm_tmul, sigma_tmul_one]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange

namespace AlgebraicGeometry.Scheme

theorem exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R
      A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd c
      (Scheme.TwoAffineOpenCover.specMap R A))
      ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U)
    ∃ e : (A ⊗[R] Γ(X, U)) ≃ₐ[A]
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U),
      ∀ s : Γ(X, U), e ((1 : A) ⊗ₜ[R] s) =
        ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app U).hom s :=
  ⟨TwoAffineOpenCover.AffineBaseChange.algEquiv c A U hU,
    TwoAffineOpenCover.AffineBaseChange.algEquiv_one_tmul c A U hU⟩

end AlgebraicGeometry.Scheme

end

end AffinePullbackSectionTensor

section AffinePullbackTensorSections

/-!
# exists alg Equiv sections pullback fst preimage tensor of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem
  _root_.AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H] :
    letI _instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V =>
      Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI _instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
        Algebra K Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap K H))) ≫ f) W
    ∃ ε : ∀ (V : A.Opens) (_ : IsAffineOpen V),
        Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V)
              ⊗[K] H,
      (∀ (V : A.Opens) (_ : IsAffineOpen V),
          IsAffineOpen ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
          ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) =
            a ⊗ₜ[K] (1 : H)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
          ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
              ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h) ∧
      (∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
          (s : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K
            H) (ε V hV s) =
            ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map
              (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K
                H)))).preimage_mono hle)).op).hom s)) := by
  let SKH := Spec.map (CommRingCat.ofHom (algebraMap K H))
  let P := pullback f SKH
  let p₁ := pullback.fst f SKH
  let p₂ := pullback.snd f SKH
  let instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f
    V
  let instKP : ∀ W : P.Opens, Algebra K Γ(P, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom
    (p₁ ≫ f) W
  let instHP : ∀ W : P.Opens, Algebra H Γ(P, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom
    p₂ W
  have towerP : ∀ W : P.Opens, IsScalarTower K H Γ(P, W) := by
    intro W
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change ((p₁ ≫ f).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of K)).inv.hom k) =
      (p₂.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom (algebraMap K H k))
    have h1 : (p₁ ≫ f).appLE ⊤ W le_top = (p₂ ≫ SKH).appLE ⊤ W le_top := by
      simp only [p₁, p₂, pullback.condition]
    rw [h1, ← Scheme.Hom.appLE_comp_appLE p₂ SKH ⊤ ⊤ W le_top le_top]
    change (p₂.appLE ⊤ W le_top).hom ((SKH.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of K)).inv.hom
      k)) = _
    congr 1
    have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K H))
    have h3 : SKH.appLE ⊤ ⊤ le_top = SKH.appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [h3]
    exact (congrArg (fun φ => φ.hom k) h2).symm
  have key : ∀ (V : A.Opens) (hV : IsAffineOpen V),
      ∃ ε : Γ(P, p₁ ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
        (∀ a : Γ(A, V), ε ((p₁.app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
        (∀ h : H, ε ((p₂.appLE ⊤ (p₁ ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom h)) = (1
          : Γ(A, V)) ⊗ₜ[K] h) := by
    intro V hV
    obtain ⟨e, he⟩ := Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
      f V hV H
    let ε : Γ(P, p₁ ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H :=
      ((e.restrictScalars K).symm).trans (Algebra.TensorProduct.comm K H Γ(A, V))
    refine ⟨ε, fun a => ?_, fun h => ?_⟩
    · change Algebra.TensorProduct.comm K H Γ(A, V) (e.symm ((p₁.app V).hom a)) = a ⊗ₜ[K] 1
      rw [← he a, e.symm_apply_apply, Algebra.TensorProduct.comm_tmul]
    · change Algebra.TensorProduct.comm K H Γ(A, V) (e.symm (algebraMap H Γ(P, p₁ ⁻¹ᵁ V) h)) = 1
        ⊗ₜ[K] h
      rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply,
        Algebra.TensorProduct.comm_tmul]
  choose ε hε₁ hε₂ using key
  have : IsAffineHom p₁ := Scheme.TwoAffineOpenCover.isAffineHom_fst f H
  refine ⟨ε, fun V hV => hV.preimage p₁, fun V hV a => hε₁ V hV a, fun V hV h => hε₂ V hV h, ?_⟩
  intro V V' hV hV' hle s
  obtain ⟨t, rfl⟩ := (ε V hV).symm.surjective s
  rw [AlgEquiv.apply_symm_apply]
  let F₁ : Γ(A, V) ⊗[K] H →ₐ[K] Γ(A, V') ⊗[K] H :=
    Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H)
  let res : Γ(P, p₁ ⁻¹ᵁ V) →ₐ[K] Γ(P, p₁ ⁻¹ᵁ V') := Scheme.TwoAffineOpenCover.restrictAlgHom (p₁ ≫
    f) (p₁.preimage_mono hle)
  let F₂ : Γ(A, V) ⊗[K] H →ₐ[K] Γ(A, V') ⊗[K] H :=
    ((ε V' hV').toAlgHom.comp res).comp (ε V hV).symm.toAlgHom
  have hF : F₁ = F₂ := by
    apply Algebra.TensorProduct.ext'
    intro a h
    change Algebra.TensorProduct.map _ _ (a ⊗ₜ[K] h) = ε V' hV' (res ((ε V hV).symm (a ⊗ₜ[K] h)))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hsplit : a ⊗ₜ[K] h = (a ⊗ₜ[K] (1 : H)) * ((1 : Γ(A, V)) ⊗ₜ[K] h) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, ← hε₁ V hV a, ← hε₂ V hV h, ← map_mul, AlgEquiv.symm_apply_apply, map_mul, map_mul]
    have hr₁ : res ((p₁.app V).hom a) = (p₁.app V').hom ((A.presheaf.map (homOfLE hle).op).hom a)
      := by
      change (p₁.appLE V (p₁ ⁻¹ᵁ V') (p₁.preimage_mono hle)).hom a = (A.presheaf.map (homOfLE
        hle).op ≫ p₁.app V').hom a
      rw [Scheme.Hom.app_eq_appLE p₁ (U := V'), Scheme.Hom.map_appLE]
    have hr₂ : res ((p₂.appLE ⊤ (p₁ ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom h)) =
        (p₂.appLE ⊤ (p₁ ⁻¹ᵁ V') le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom h) := by
      change (P.presheaf.map (homOfLE (p₁.preimage_mono hle)).op).hom ((p₂.appLE ⊤ (p₁ ⁻¹ᵁ V)
        le_top).hom _) = _
      rw [← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_map]
    rw [hr₁, hr₂, hε₁ V' hV', hε₂ V' hV', Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  exact congrArg (fun F : Γ(A, V) ⊗[K] H →ₐ[K] Γ(A, V') ⊗[K] H => F t) hF
end exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

end AffinePullbackTensorSections
