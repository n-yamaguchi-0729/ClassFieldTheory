/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Nyll.SchemeTheory.Morphisms.AppLECongr
public import Nyll.SchemeTheory.Affine.ClosedBaseChangeSections

/-!
# Local section lifts in a closed base change

A scheme over an affine base is restricted to a quotient of its base ring.
The quotient of sections on an affine open has the expected mapped ideal,
and local lifts are compatible with restriction and further base change.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open AlgebraicGeometry.Scheme.Hom (le_preimage_top)

namespace AlgebraicGeometry.ClosedBaseChangeLifts

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (p : X ⟶ Spec A)

/-- The quotient-ring morphism associated with a base ideal. -/
abbrev quot (I : Ideal A) : A ⟶ CommRingCat.of (A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)

/-- The closed base change of the scheme along an ideal quotient. -/
abbrev XI (I : Ideal A) : Scheme.{u} := pullback p (Spec.map (quot I))

/-- The projection from the closed base change to the original scheme. -/
abbrev ι (I : Ideal A) : XI p I ⟶ X := pullback.fst _ _
/-- The structure morphism of the closed base change. -/
abbrev pI (I : Ideal A) : XI p I ⟶ Spec (.of (A ⧸ I)) := pullback.snd _ _

/-- The original base-ring action on sections of an open subscheme. -/
noncomputable def alg (U : X.Opens) : A →+* Γ(X, U) :=
  (p.appLE ⊤ U (le_preimage_top p U)).hom.comp (Scheme.ΓSpecIso A).inv.hom

/-- The quotient-ring action on global sections of the closed base change. -/
noncomputable def φ (I : Ideal A) : A ⧸ I →+* Γ(XI p I, ⊤) :=
  ((pI p I).appTop).hom.comp (Scheme.ΓSpecIso (.of (A ⧸ I))).inv.hom

/-- The coefficient homomorphisms agree under restriction. -/
lemma alg_map {U V : X.Opens} (i : V ≤ U) (a : A) :
    X.presheaf.map (homOfLE i).op (alg p U a) = alg p V a := by
  simp only [alg, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/--
Over an affine open, quotient base change on sections is surjective with the mapped ideal as kernel.
-/
lemma ker_ι_app (I : Ideal A) {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker ((ι p I).app U).hom = I.map (alg p U) ∧ Function.Surjective ((ι p I).app U) := by
  let h : IsPullback (ι p I) (pI p I) p (Spec.map (quot I)) := IsPullback.of_hasPullback _ _
  have hφ : Function.Surjective (quot I).hom := Ideal.Quotient.mk_surjective
  have hker := Scheme.Hom.ker_app_of_closed_baseChange p (pI p I) (ι p I) (quot I) h hφ U hU
  have hquot : RingHom.ker (quot I).hom = I := Ideal.mk_ker
  rw [hquot] at hker
  exact ⟨hker, Scheme.Hom.surjective_app_of_closed_baseChange p (pI p I) (ι p I) (quot I) h hφ U hU⟩

/-- A section over an open lifts the restriction of a section of the closed base change. -/
def LiftsAt (I : Ideal A) (U : X.Opens) (t : Γ(XI p I, ⊤)) (c : Γ(X, U)) : Prop :=
  (ι p I).app U c = (XI p I).presheaf.map (homOfLE le_top).op t

/-- Over an affine open every restricted quotient section admits a lift. -/
lemma LiftsAt.exists (I : Ideal A) {U : X.Opens} (hU : IsAffineOpen U) (t : Γ(XI p I, ⊤)) :
    ∃ c, LiftsAt p I U t c :=
  (ker_ι_app p I hU).2 _

/-- Zero lifts zero on every open. -/
lemma LiftsAt.zero (I : Ideal A) (U : X.Opens) : LiftsAt p I U 0 0 := by
  simp only [LiftsAt, map_zero]

/-- The sum of local lifts lifts the sum. -/
lemma LiftsAt.add {I : Ideal A} {U : X.Opens} {t t' : Γ(XI p I, ⊤)} {c c' : Γ(X, U)}
    (h : LiftsAt p I U t c) (h' : LiftsAt p I U t' c') : LiftsAt p I U (t + t') (c + c') := by
  simp only [LiftsAt, map_add] at *; rw [h, h']

/-- The difference of local lifts lifts the difference. -/
lemma LiftsAt.sub {I : Ideal A} {U : X.Opens} {t t' : Γ(XI p I, ⊤)} {c c' : Γ(X, U)}
    (h : LiftsAt p I U t c) (h' : LiftsAt p I U t' c') : LiftsAt p I U (t - t') (c - c') := by
  simp only [LiftsAt, map_sub] at *; rw [h, h']

/-- The product of local lifts lifts the product. -/
lemma LiftsAt.mul {I : Ideal A} {U : X.Opens} {t t' : Γ(XI p I, ⊤)} {c c' : Γ(X, U)}
    (h : LiftsAt p I U t c) (h' : LiftsAt p I U t' c') : LiftsAt p I U (t * t') (c * c') := by
  simp only [LiftsAt, map_mul] at *; rw [h, h']

/-- Two affine lifts of the same section differ by the mapped ideal. -/
lemma LiftsAt.sub_mem_iff {I : Ideal A} {U : X.Opens} (hU : IsAffineOpen U) {t : Γ(XI p I, ⊤)}
    {c c' : Γ(X, U)} (h : LiftsAt p I U t c) :
    LiftsAt p I U t c' ↔ c - c' ∈ I.map (alg p U) := by
  rw [← (ker_ι_app p I hU).1, RingHom.mem_ker, map_sub, sub_eq_zero]
  unfold LiftsAt at *
  rw [h]
  exact eq_comm

/-- An affine local section lifts zero exactly when it lies in the mapped ideal. -/
lemma LiftsAt.mem_iff_of_zero {I : Ideal A} {U : X.Opens} (hU : IsAffineOpen U) {c : Γ(X, U)} :
    LiftsAt p I U 0 c ↔ c ∈ I.map (alg p U) := by
  have := (LiftsAt.zero p I U).sub_mem_iff p hU (c' := c)
  rw [zero_sub, neg_mem_iff] at this
  exact this

/-- A local lift restricts to a lift on every smaller open. -/
lemma LiftsAt.restrict {I : Ideal A} {U V : X.Opens} (i : V ≤ U) {t : Γ(XI p I, ⊤)} {c : Γ(X, U)}
    (h : LiftsAt p I U t c) : LiftsAt p I V t (X.presheaf.map (homOfLE i).op c) := by
  unfold LiftsAt at *
  have := (ι p I).naturality (homOfLE i).op
  have h2 := congrArg (fun φ => φ.hom c) this
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  change (ι p I).app V (X.presheaf.map (homOfLE i).op c) = _
  rw [← CommRingCat.comp_apply, this, CommRingCat.comp_apply, h, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  rfl

/-- The coefficient homomorphism gives the local lift of a quotient scalar section. -/
lemma LiftsAt.alg (I : Ideal A) (U : X.Opens) (a : A) :
    LiftsAt p I U (φ p I (Ideal.Quotient.mk I a)) (alg p U a) := by
  let V := (ι p I) ⁻¹ᵁ U
  let coeff := ((pI p I).constToPresheaf.app (op V)).hom
  change (ι p I).app U (ClosedBaseChangeLifts.alg p U a) =
    (XI p I).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ p I (Ideal.Quotient.mk I a))
  calc
    _ = ((((ι p I) ≫ p).constToPresheaf.app (op V)).hom) a :=
      DFunLike.congr_fun (Scheme.Hom.constToPresheaf_comp_app (ι p I) p U) a
    _ = coeff (Ideal.Quotient.mk I a) := by
      rw [pullback.condition, Scheme.Hom.constToPresheaf_comp_Spec_map]
      rfl
    _ = (XI p I).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (ClosedBaseChangeLifts.alg (pI p I) ⊤ (Ideal.Quotient.mk I a)) :=
      (alg_map (pI p I) (le_top : V ≤ ⊤) (Ideal.Quotient.mk I a)).symm
    _ = _ := by
      have h := (pI p I).appLE_top_eq_appTop
      unfold ClosedBaseChangeLifts.alg φ
      rw [h]

/-- A global quotient section vanishes if it vanishes on all pulled back affine opens. -/
lemma eq_zero_of_forall_affine (I : Ideal A) (t : Γ(XI p I, ⊤))
    (h : ∀ U : X.affineOpens,
      (XI p I).presheaf.map (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ U))).op t = 0) :
    t = 0 := by
  have hcov : (⊤ : (XI p I).Opens) ≤ ⨆ U : X.affineOpens, (ι p I) ⁻¹ᵁ (U : X.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top
  refine TopCat.Sheaf.eq_of_locally_eq' (XI p I).sheaf
    (fun U : X.affineOpens => (ι p I) ⁻¹ᵁ (U : X.Opens))
    ⊤ (fun U => homOfLE le_top) hcov t 0 ?_
  intro U
  rw [map_zero]
  exact h U

/-- A quotient section lifted locally by zero vanishes. -/
lemma eq_zero_of_forall_liftsAt (I : Ideal A) (t : Γ(XI p I, ⊤))
    (h : ∀ U : X.affineOpens, ∀ c, LiftsAt p I U t c → c ∈ I.map (alg p U)) : t = 0 := by
  apply eq_zero_of_forall_affine
  intro U
  obtain ⟨c, hc⟩ := LiftsAt.exists p I U.2 t
  have := h U c hc
  rw [← (ker_ι_app p I U.2).1, RingHom.mem_ker] at this
  unfold LiftsAt at hc
  rw [← hc]
  exact this

/-- Two quotient sections with the same local lifts are equal. -/
lemma eq_of_forall_liftsAt (I : Ideal A) (t t' : Γ(XI p I, ⊤))
    (h : ∀ U : X.affineOpens, ∃ c, LiftsAt p I U t c ∧ LiftsAt p I U t' c) : t = t' := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_liftsAt
  intro U c hc
  obtain ⟨d, hd, hd'⟩ := h U
  have h0 : LiftsAt p I U (t - t') 0 := by simpa only [sub_self] using hd.sub p hd'
  have := (h0.sub_mem_iff p U.2).mp hc
  simpa only [zero_sub, neg_mem_iff] using this

/-- Restrictions along parallel maps of opens agree. -/
lemma presheaf_map_congr {Y : Scheme.{u}} {U V : Y.Opens} (i j : op U ⟶ op V) (s : Γ(Y, U)) :
    Y.presheaf.map i s = Y.presheaf.map j s := by
  rw [Subsingleton.elim i j]

/-- A global lift gives a local lift after restriction. -/
lemma LiftsAt.of_appTop (I : Ideal A) (U : X.Opens) (a : Γ(X, ⊤)) :
    LiftsAt p I U ((ι p I).appTop a) (X.presheaf.map (homOfLE (le_top (a := U))).op a) := by
  unfold LiftsAt
  have nat := (ι p I).naturality (homOfLE (le_top (a := U))).op
  have h2 := congrArg (fun φ => φ.hom a) nat
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  change ((ι p I).app U) ((X.presheaf.map (homOfLE le_top).op) a) = _
  erw [h2]
  exact presheaf_map_congr _ _ _

/-- A local lift remains a lift under a compatible further base change. -/
lemma LiftsAt.trans_of {I J : Ideal A} (τ : XI p J ⟶ XI p I) (hτ : τ ≫ ι p I = ι p J)
    {U : X.Opens} {t : Γ(XI p I, ⊤)} {c : Γ(X, U)}
    (h : LiftsAt p I U t c) : LiftsAt p J U (τ.appTop t) c := by
  unfold LiftsAt at h ⊢
  have hpre : (ι p J) ⁻¹ᵁ U = τ ⁻¹ᵁ ((ι p I) ⁻¹ᵁ U) := by
    rw [← hτ, Scheme.Hom.comp_preimage]
  let τU : Γ(XI p I, (ι p I) ⁻¹ᵁ U) ⟶ Γ(XI p J, (ι p J) ⁻¹ᵁ U) :=
    τ.appLE ((ι p I) ⁻¹ᵁ U) ((ι p J) ⁻¹ᵁ U) hpre.le
  have hcomp : (ι p I).app U ≫ τU = (ι p J).app U := by
    change (ι p I).app U ≫
      τ.appLE ((ι p I) ⁻¹ᵁ U) ((ι p J) ⁻¹ᵁ U) hpre.le = (ι p J).app U
    rw [← (ι p I).appLE_eq_app]
    exact (Scheme.Hom.appLE_comp_appLE τ (ι p I) U
      ((ι p I) ⁻¹ᵁ U) ((ι p J) ⁻¹ᵁ U) le_rfl hpre.le).trans
      ((Scheme.Hom.appLE_congr_hom hτ U ((ι p J) ⁻¹ᵁ U) _ le_rfl).trans
        (ι p J).appLE_eq_app)
  have hmap : (XI p I).presheaf.map (homOfLE le_top).op ≫ τU =
      τ.appTop ≫ (XI p J).presheaf.map (homOfLE le_top).op :=
    τ.map_appLE hpre.le (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ U))).op
  calc
    (ι p J).app U c = τU ((ι p I).app U c) :=
      (congrArg (fun ψ : Γ(X, U) ⟶ Γ(XI p J, (ι p J) ⁻¹ᵁ U) => ψ c) hcomp).symm
    _ = τU ((XI p I).presheaf.map (homOfLE le_top).op t) := congrArg τU h
    _ = (XI p J).presheaf.map (homOfLE le_top).op (τ.appTop t) :=
      congrArg (fun ψ : Γ(XI p I, ⊤) ⟶ Γ(XI p J, (ι p J) ⁻¹ᵁ U) => ψ t) hmap

/-- Local lifts on an open cover determine the quotient section. -/
lemma eq_of_forall_liftsAt_cover (I : Ideal A) {κ : Type*} (W : κ → X.Opens)
    (hcov : ⨆ k, W k = ⊤) (t t' : Γ(XI p I, ⊤))
    (h : ∀ k, ∃ c, LiftsAt p I (W k) t c ∧ LiftsAt p I (W k) t' c) : t = t' := by
  have hcov' : (⊤ : (XI p I).Opens) ≤ ⨆ k, (ι p I) ⁻¹ᵁ (W k) := by
    rw [← Scheme.Hom.preimage_iSup, hcov]
    exact le_top
  refine TopCat.Sheaf.eq_of_locally_eq' (XI p I).sheaf (fun k => (ι p I) ⁻¹ᵁ (W k))
    ⊤ (fun k => homOfLE le_top) hcov' t t' ?_
  intro k
  obtain ⟨c, hc, hc'⟩ := h k
  unfold LiftsAt at hc hc'
  exact hc.symm.trans hc'

end AlgebraicGeometry.ClosedBaseChangeLifts
