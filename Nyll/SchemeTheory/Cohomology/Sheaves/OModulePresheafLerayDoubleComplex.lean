/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDCompD
public import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex
public import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverOf
public import Nyll.SchemeTheory.Cohomology.Sheaves.DoubleComplex

/-!
The double-complex structure, augmentations and total cohomology of the Leray bicomplex.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.OModulePresheaf.Leray

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem map_iInf_fin {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (U : Fin (n + 1) → Y.Opens) :
    (TopologicalSpace.Opens.map f.base).obj (⨅ j, U j) = ⨅ j, (TopologicalSpace.Opens.map
      f.base).obj (U j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero => simp only [show (⨅ j : Fin 1, U j) = U 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, (TopologicalSpace.Opens.map f.base).obj (U j)) =
        (TopologicalSpace.Opens.map f.base).obj (U 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit U, show (TopologicalSpace.Opens.map f.base).obj (U 0 ⊓ (⨅ j : Fin (m + 1), U j.succ))
        = (TopologicalSpace.Opens.map f.base).obj (U 0) ⊓ (TopologicalSpace.Opens.map f.base).obj
          (⨅ j : Fin (m + 1), U j.succ)
      from rfl, ih (fun j => U j.succ), hsplit (fun j => (TopologicalSpace.Opens.map f.base).obj
        (U j))]

section DblCpx

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

theorem dV_sq (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dV p πZ K K' a (b + 1) ∘ₗ dV p πZ K K' a b = 0 := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun x => (biC_uncurry p πZ K K' a (b + 2)).injective (funext fun σ => ?_)
  have h₁ := dV_uncurry p πZ K K' a (b + 1) (dV p πZ K K' a b x) σ
  rw [dV_uncurry p πZ K K' a b x σ, relAltd_eq_d, relAltd_eq_d] at h₁
  exact (h₁.trans (OModulePresheaf.d_comp_d_apply (pushOpen p πZ (K.inter σ)) K' b _)).trans
    (congrFun (map_zero (biC_uncurry p πZ K K' a (b + 2))) σ).symm

theorem dH_sq (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dH p πZ K K' (a + 1) b ∘ₗ dH p πZ K K' a b = 0 := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun x => (biC_uncurry' p πZ K K' (a + 2) b).injective (funext fun τ => ?_)
  have h₁ := dH_uncurry p πZ K K' (a + 1) b (dH p πZ K K' a b x) τ
  rw [dH_uncurry p πZ K K' a b x τ] at h₁
  exact (h₁.trans (OModulePresheaf.d_comp_d_apply (pullOpen p πZ (K'.inter τ)) K a _)).trans
    (congrFun (map_zero (biC_uncurry' p πZ K K' (a + 2) b)) τ).symm

theorem dHV_comm (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dV p πZ K K' (a + 1) b ∘ₗ dH p πZ K K' a b = dH p πZ K K' a (b + 1) ∘ₗ dV p πZ K K' a b := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun x => funext fun στ => ?_
  simp only [LinearMap.comp_apply, dH_apply', dV_apply', map_sum, map_zsmul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  erw [Scheme.TwoAffineOpenCover.res_res, Scheme.TwoAffineOpenCover.res_res]

/-- The bounded double complex formed by horizontal and vertical Čech differentials. -/
def LerayDblCpx : DoubleComplex.Bounded R :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { C := biC p πZ K K'
    dH := dH p πZ K K'
    dV := dV p πZ K K'
    dH_sq := dH_sq p πZ K K'
    dV_sq := dV_sq p πZ K K'
    dHV_comm := dHV_comm p πZ K K'
    N := max (Fintype.card K.ι) (Fintype.card K'.ι)
    hBound := biC_subsingleton p πZ K K' }

theorem LerayDblCpx_C (a b : ℕ) : (LerayDblCpx p πZ K K').C a b = biC p πZ K K' a b := rfl
theorem LerayDblCpx_N : (LerayDblCpx p πZ K K').N = max (Fintype.card K.ι) (Fintype.card K'.ι) :=
    rfl
theorem LerayDblCpx_dH (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (LerayDblCpx p πZ K K').dH a b = dH p πZ K K' a b := rfl
theorem LerayDblCpx_dV (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (LerayDblCpx p πZ K K').dV a b = dV p πZ K K' a b := rfl

/-- The augmentation from source Čech cochains to the horizontal degree-zero column. -/
def biAug (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (OModulePresheaf.unit (p ≫ πZ)).cochain K' b →ₗ[R] biC p πZ K K' 0 b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun στ => Scheme.OrderedAffineCoverOf.res (p ≫ πZ) inf_le_left ∘ₗ LinearMap.proj στ.2

theorem biAug_apply (b : ℕ) (y : (OModulePresheaf.unit (p ≫ πZ)).cochain K' b) (στ : BiIdx K K' 0
    b) :
    biAug p πZ K K' b y στ
      = (V'.presheaf.map (homOfLE (inf_le_left : biOpen p K K' 0 b στ.1 στ.2 ≤ K'.inter
        στ.2)).op).hom (y στ.2) :=
  rfl

end DblCpx

section RelAug

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) (K' : Scheme.OrderedAffineCover V') (U :
  Z.Opens)

/-- The augmentation from sections on a preimage open to relative Čech cochains. -/
def relAug :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (pullOpen p πZ (⊤ : V'.Opens)).obj U →ₗ[R] relAltC p πZ K' U 0 :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun _ => Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inf_le_inf_right _ le_top)

theorem relAug_apply (w : (pullOpen p πZ (⊤ : V'.Opens)).obj U) (τ : K'.Idx 0) :
    relAug p πZ K' U w τ
      = (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U)
          (le_top : K'.inter τ ≤ ⊤))).op).hom w :=
  rfl

end RelAug

section RowCover

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ] [IsSeparated (p ≫ πZ)]
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

/-- The affine cover of a vertical intersection induced by the base affine cover. -/
def rowCoverOf {q : ℕ} (τ : K'.Idx q) : V'.OrderedAffineCoverOf (K'.inter τ) where
  ι := K.ι
  U i := K'.inter τ ⊓ (Opens.map p.base).obj (K.U i)
  isAffineOpen i := Scheme.OrderedAffineCover.fiberAffineOpen p πZ
    (Scheme.OrderedAffineCover.isAffineOpen_inter (p ≫ πZ) K' τ) (K.isAffineOpen i)
  le _ := inf_le_left
  iSup_eq := le_antisymm (iSup_le fun _ => inf_le_left) fun x hx =>
    let ⟨i, hi⟩ := Opens.mem_iSup.mp (show p.base x ∈ ⨆ i, K.U i from K.iSup_eq_top.symm ▸ trivial)
    Opens.mem_iSup.mpr ⟨i, hx, hi⟩

theorem rowCoverOf_U {q : ℕ} (τ : K'.Idx q) (i : K.ι) :
    (rowCoverOf p πZ K K' τ).U i = K'.inter τ ⊓ (Opens.map p.base).obj (K.U i) := rfl

theorem inter_rowCoverOf {a b : ℕ} (τ : K'.Idx b) (σ : (rowCoverOf p πZ K K' τ).Idx a) :
    (rowCoverOf p πZ K K' τ).inter σ = biOpen p K K' a b σ τ := by
  change (⨅ j, K'.inter τ ⊓ (Opens.map p.base).obj (K.U (σ.1 j)))
    = K'.inter τ ⊓ (Opens.map p.base).obj (⨅ j, K.U (σ.1 j))
  rw [map_iInf_fin p (fun j => K.U (σ.1 j)), ← inf_iInf]

end RowCover

section RestrictToPreimage

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ] (K' :
  Scheme.OrderedAffineCover V')

theorem inter_restrictToPreimage {U : Z.Opens} (hU : IsAffineOpen U) {b : ℕ}
    (τ : (restrictToPreimage p πZ K' hU).Idx b) :
    (restrictToPreimage p πZ K' hU).inter τ = K'.inter τ ⊓ (Opens.map p.base).obj U := by
  change (⨅ j, K'.U (τ.1 j) ⊓ (Opens.map p.base).obj U) = (⨅ j, K'.U (τ.1 j)) ⊓ (Opens.map
    p.base).obj U
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end RestrictToPreimage

end AlgebraicGeometry.OModulePresheaf.Leray

end
