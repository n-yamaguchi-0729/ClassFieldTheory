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

public import Nyll.SchemeTheory.Morphisms.ClosedBaseChangeLifts
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDEqDDMemPow
public import Nyll.SchemeTheory.Morphisms.AppLECongr

/-!
# Lifting sections through powers of a base ideal

Affine local lifts and ideal-power control of Čech coboundaries produce global
sections after restricting from a sufficiently thick closed base change.
-/

@[expose] public section

section ProofImplementation

open AlgebraicGeometry.Scheme.Hom (le_preimage_top)

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance]
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp]
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq


open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

open _root_.AlgebraicGeometry.ClosedBaseChangeLifts

noncomputable section

namespace SolML0C

variable {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))

section Cover

variable [CompactSpace P]

/-- Choose a finite ordered affine cover of a compact scheme. -/
noncomputable def cover (P : Scheme.{u}) [CompactSpace P] : P.OrderedAffineCover :=
  let 𝒰 := P.affineCover.finiteSubcover
  let : LinearOrder 𝒰.I₀ :=
    LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
  { ι := 𝒰.I₀
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable (K : P.OrderedAffineCover)

/-- The degree-zero index represented by a single cover member. -/
def vtx (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by
  have : a = b := (Fin.eq_zero a).trans (Fin.eq_zero b).symm
  subst a
  exact lt_irrefl b)⟩

lemma idx0_eq_vtx (s : K.Idx 0) : s = vtx K (s.1 0) := by
  apply Subtype.ext
  funext k
  have hk : k = 0 := Fin.eq_zero k
  subst hk; rfl

/-- The degree-one index represented by an increasing pair of cover members. -/
def edge {i j : K.ι} (h : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr (fun k => by
    have hk : k = 0 := Fin.eq_zero k
    subst hk
    exact h)⟩

lemma face_edge_zero {i j : K.ι} (h : i < j) : K.face (edge K h) 0 = vtx K j := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.eq_zero k
  subst hk
  change (![i, j] : Fin 2 → K.ι) ((0 : Fin 2).succAbove 0) = j
  exact congrArg (![i, j] : Fin 2 → K.ι) (Fin.succAbove_zero_apply (0 : Fin 1))

lemma face_edge_one {i j : K.ι} (h : i < j) : K.face (edge K h) 1 = vtx K i := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.eq_zero k
  subst hk
  change (![i, j] : Fin 2 → K.ι) ((Fin.last 1).succAbove 0) = i
  exact congrArg (![i, j] : Fin 2 → K.ι) (Fin.succAbove_last_apply (0 : Fin 1))

lemma inter_edge_le_left {i j : K.ι} (h : i < j) : K.inter (edge K h) ≤ K.inter (vtx K i) :=
  le_iInf fun _ => (K.inter_le (edge K h) 0).trans (le_of_eq rfl)

lemma inter_edge_le_right {i j : K.ι} (h : i < j) : K.inter (edge K h) ≤ K.inter (vtx K j) :=
  le_iInf fun _ => (K.inter_le (edge K h) 1).trans (le_of_eq rfl)

lemma inf_vtx_le_inter_edge {i j : K.ι} (h : i < j) :
    K.inter (vtx K i) ⊓ K.inter (vtx K j) ≤ K.inter (edge K h) := by
  refine le_iInf fun k => ?_
  fin_cases k
  · exact inf_le_left.trans ((K.inter_le (vtx K i) 0).trans (le_of_eq rfl))
  · exact inf_le_right.trans ((K.inter_le (vtx K j) 0).trans (le_of_eq rfl))

lemma U_le_inter_vtx (i : K.ι) : K.U i ≤ K.inter (vtx K i) := le_iInf fun _ => le_rfl

lemma iSup_inter_vtx : (⊤ : P.Opens) ≤ ⨆ i, K.inter (vtx K i) := by
  rw [← K.iSup_eq_top]
  exact iSup_mono fun i => U_le_inter_vtx K i

/-- Restrict a global section to the zero-cochain on an ordered affine cover. -/
noncomputable def toCochain :
    (OModulePresheaf.unit q).obj ⊤ →ₗ[A] (OModulePresheaf.unit q).cochain K 0 :=
  LinearMap.pi fun s => (OModulePresheaf.unit q).res (le_top : K.inter s ≤ ⊤)

lemma toCochain_apply (x : (OModulePresheaf.unit q).obj ⊤) (s : K.Idx 0) :
    toCochain q K x s = (OModulePresheaf.unit q).res (le_top : K.inter s ≤ ⊤) x := rfl

lemma d_toCochain (x : (OModulePresheaf.unit q).obj ⊤) :
    (OModulePresheaf.unit q).d K 0 (toCochain q K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply]
  simp only [toCochain_apply, OModulePresheaf.res_res, Pi.zero_apply]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_one_smul, add_neg_cancel]

lemma range_toCochain_le : LinearMap.range (toCochain q K) ≤ (OModulePresheaf.unit q).H0 K := by
  rintro _ ⟨x, rfl⟩
  exact d_toCochain q K x

lemma toCochain_injective : Function.Injective (toCochain q K) := by
  intro x y hxy
  refine P.sheaf.eq_of_locally_eq' (fun i => K.inter (vtx K i)) ⊤ (fun i => homOfLE le_top)
    (iSup_inter_vtx K) x y fun i => ?_
  exact congr_fun hxy (vtx K i)

lemma toCochain_surjective (c : (OModulePresheaf.unit q).cochain K 0)
    (hc : (OModulePresheaf.unit q).d K 0 c = 0) : ∃ x, toCochain q K x = c := by
  let sf : ∀ i : K.ι, Γ(P, K.inter (vtx K i)) := fun i => c (vtx K i)
  have key : ∀ {i j : K.ι} (h : i < j),
      (P.presheaf.map (homOfLE (inter_edge_le_left K h)).op).hom (sf i) =
        (P.presheaf.map (homOfLE (inter_edge_le_right K h)).op).hom (sf j) := by
    intro i j h
    have := congr_fun hc (edge K h)
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at this
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      Pi.zero_apply] at this
    rw [add_neg_eq_zero] at this
    have h0 := face_edge_zero K h
    have h1 := face_edge_one K h
    have e0 : ∀ (t : K.Idx 0) (ht : t = vtx K j) (le : K.inter (edge K h) ≤ K.inter t),
        (OModulePresheaf.unit q).res le (c t) =
          (P.presheaf.map (homOfLE (inter_edge_le_right K h)).op).hom (sf j) := by
      rintro t rfl le; rfl
    have e1 : ∀ (t : K.Idx 0) (ht : t = vtx K i) (le : K.inter (edge K h) ≤ K.inter t),
        (OModulePresheaf.unit q).res le (c t) =
          (P.presheaf.map (homOfLE (inter_edge_le_left K h)).op).hom (sf i) := by
      rintro t rfl le; rfl
    rw [e0 _ h0, e1 _ h1] at this
    exact this.symm
  have hcompat : TopCat.Presheaf.IsCompatible P.presheaf (fun i => K.inter (vtx K i)) sf := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have := congr_arg (P.presheaf.map (homOfLE (inf_vtx_le_inter_edge K hij)).op).hom (key hij)
      simp only [← CommRingCat.comp_apply, ← P.presheaf.map_comp] at this
      exact this
    · rfl
    · have := congr_arg (P.presheaf.map (homOfLE ((le_of_eq (inf_comm _ _)).trans
        (inf_vtx_le_inter_edge K hji))).op).hom (key hji)
      simp only [← CommRingCat.comp_apply, ← P.presheaf.map_comp] at this
      exact this.symm
  obtain ⟨x, hx, -⟩ := P.sheaf.existsUnique_gluing' (fun i => K.inter (vtx K i)) ⊤
    (fun i => homOfLE le_top) (iSup_inter_vtx K) sf hcompat
  refine ⟨x, funext fun s => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, s = vtx K i := ⟨_, idx0_eq_vtx K s⟩
  exact hx i

end H0

end SolML0C

end

noncomputable section

namespace SolML0

open SolML0C

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]

theorem main (n : ℕ) :
    ∃ c : ℕ, ∀ t :
      Γ(pullback q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + c))))), ⊤),
      ∃ a : Γ(P, ⊤),
        (pullback.map q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))
            q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + c)))))
            (𝟙 P) (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n c)))))
            (𝟙 _) (by rw [Category.id_comp, Category.comp_id]) (by
              rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                Ideal.Quotient.factor_comp_mk])).appTop t =
          (pullback.fst q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))).appTop a := by
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (pullback.diagonal (terminal.from P)) := by
    have : IsSeparated (terminal.from P) := by rw [← terminal.comp_from q]; infer_instance
    infer_instance
  let K := SolML0C.cover P
  obtain ⟨c, hc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper I q K n
  refine ⟨c, fun t => ?_⟩
  set τ : XI (A := CommRingCat.of A) q (I ^ n) ⟶ XI (A := CommRingCat.of A) q (I ^ (n + c)) :=
    pullback.map q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))
      q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + c)))))
      (𝟙 P) (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n c)))))
      (𝟙 _) (by rw [Category.id_comp, Category.comp_id]) (by
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          Ideal.Quotient.factor_comp_mk]) with hτdef
  have hτ : τ ≫ ι (A := CommRingCat.of A) q (I ^ (n + c)) =
      ι (A := CommRingCat.of A) q (I ^ n) := by
    rw [hτdef, ι, pullback.lift_fst, Category.comp_id]
  have haff : ∀ {i : ℕ} (s : K.Idx i), IsAffineOpen (K.inter s) := fun s =>
    IsAffineOpen.iInf fun j => K.isAffineOpen (s.1 j)
  choose w hw using fun s : K.Idx 0 =>
    LiftsAt.exists (A := CommRingCat.of A) q (I ^ (n + c)) (haff s) t
  let wc : (OModulePresheaf.unit q).cochain K 0 := w
  have hz : ∀ e : K.Idx 1, (OModulePresheaf.unit q).d K 0 wc e ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter e) (le_preimage_top q (K.inter e))).hom
        (I ^ (n + c)) := by
    intro e
    have h0 := (hw (K.face e 0)).restrict (A := CommRingCat.of A) q (K.inter_le_inter_face e 0)
    have h1 := (hw (K.face e 1)).restrict (A := CommRingCat.of A) q (K.inter_le_inter_face e 1)
    have h01 := h0.sub (A := CommRingCat.of A) q h1
    rw [sub_self] at h01
    have hmem := (LiftsAt.mem_iff_of_zero (A := CommRingCat.of A) q (haff e)).mp h01
    have hd : (OModulePresheaf.unit q).d K 0 wc e =
        P.presheaf.map (homOfLE (K.inter_le_inter_face e 0)).op (w (K.face e 0)) -
          P.presheaf.map (homOfLE (K.inter_le_inter_face e 1)).op (w (K.face e 1)) := by
      rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
        sub_eq_add_neg]
      rfl
    rw [hd]
    exact hmem
  obtain ⟨w', hw'mem, hdw'⟩ := hc wc hz
  have hdv : (OModulePresheaf.unit q).d K 0 (wc - w') = 0 := by rw [map_sub, hdw', sub_self]
  obtain ⟨a, ha⟩ := SolML0C.toCochain_surjective q K (wc - w') hdv
  refine ⟨a, ?_⟩
  have hcov : ⨆ i, K.inter (SolML0C.vtx K i) = ⊤ := top_le_iff.mp (SolML0C.iSup_inter_vtx K)
  apply eq_of_forall_liftsAt_cover (A := CommRingCat.of A) q (I ^ n)
    (fun i => K.inter (SolML0C.vtx K i)) hcov
  intro i
  refine ⟨w (SolML0C.vtx K i), (hw _).trans_of (A := CommRingCat.of A) q τ hτ, ?_⟩
  have h1 := LiftsAt.of_appTop (A := CommRingCat.of A) q (I ^ n) (K.inter (SolML0C.vtx K i)) a
  have hres : P.presheaf.map (homOfLE le_top).op a =
      w (SolML0C.vtx K i) - (show Γ(P, K.inter (SolML0C.vtx K i)) from w' (SolML0C.vtx K i)) :=
    congr_fun ha (SolML0C.vtx K i)
  rw [hres] at h1
  refine (h1.sub_mem_iff (A := CommRingCat.of A) q (haff _)).mpr ?_
  rw [sub_sub_cancel_left]
  exact neg_mem (hw'mem _)

end SolML0

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] (n : ℕ) :
    ∃ c : ℕ, ∀ t :
      Γ(pullback q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + c))))), ⊤),
      ∃ a : Γ(P, ⊤),
        (pullback.map q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))
            q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + c)))))
            (𝟙 P) (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n c)))))
            (𝟙 _) (by rw [Category.id_comp, Category.comp_id]) (by
              rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                Ideal.Quotient.factor_comp_mk])).appTop t =
          (pullback.fst q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))).appTop a :=
  SolML0.main I q n
end exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
attribute [-instance]
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
