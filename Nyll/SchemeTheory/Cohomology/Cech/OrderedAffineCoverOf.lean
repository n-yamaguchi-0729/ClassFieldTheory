/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverOf.lean
The ordered index proofs also use the following upstream source.
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Data.Finset.Sort
public import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom

/-!
# Ordered affine covers of an open subset

An ordered affine cover of an open has increasing-index Cech cochains, alternating
restriction differentials, and an augmentation from sections of the structure sheaf.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

/-- A finite linearly ordered family of affine opens covering the specified open subset. -/
structure Scheme.OrderedAffineCoverOf {V : Scheme.{u}} (W : V.Opens) where
  /-- The index type of the affine opens in the cover. -/
  ι : Type u
  /-- A finite enumeration of the cover indices. -/
  [instFintype : Fintype ι]
  /-- The linear order used to form increasing Cech indices. -/
  [instLinearOrder : LinearOrder ι]
  /-- The affine open associated with each cover index. -/
  U : ι → V.Opens
  /-- Each member of the cover is an affine open. -/
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  /-- Each member of the cover lies in the specified open subset. -/
  le : ∀ i, U i ≤ W
  /-- The supremum of the cover members is the specified open subset. -/
  iSup_eq : ⨆ i, U i = W

attribute [instance]
  Scheme.OrderedAffineCoverOf.instFintype
  Scheme.OrderedAffineCoverOf.instLinearOrder

namespace Scheme.OrderedAffineCoverOf

variable {W : V.Opens} (K : V.OrderedAffineCoverOf W)

/-- Strictly increasing tuples of cover indices for intersections in the given Cech degree. -/
def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _
instance (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

/-- The intersection of the cover members selected by an increasing tuple. -/
def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

/-- The increasing tuple obtained by deleting the specified index. -/
def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j

theorem inter_le_base {i : ℕ} (s : K.Idx i) : K.inter s ≤ W := (iInf_le _ 0).trans (K.le _)

/-- The finite set of chart indices occurring in an ordered Čech index. -/
abbrev altImg {i : ℕ} (s : K.Idx i) : Finset K.ι :=
  Finset.univ.image s.1

theorem card_altImg {i : ℕ} (s : K.Idx i) :
    (altImg K s).card = i + 1 := by
  rw [Finset.card_image_of_injective _ s.2.injective, Finset.card_univ, Fintype.card_fin]

theorem altIdx_canonical {i : ℕ} (s : K.Idx i) :
    s.1 = (altImg K s).orderEmbOfFin (card_altImg K s) :=
  Finset.orderEmbOfFin_unique _ (fun k => Finset.mem_image_of_mem _ (Finset.mem_univ k)) s.2

theorem altIdx_eq_of_altImg {i : ℕ} {s t : K.Idx i}
    (h : altImg K s = altImg K t) : s = t := by
  apply Subtype.ext
  rw [altIdx_canonical K s]
  exact (Finset.orderEmbOfFin_unique (card_altImg K s)
    (fun k => h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ k)) t.2).symm

theorem altOpen_eq_biInf {i : ℕ} (s : K.Idx i) :
    K.inter s = ⨅ j ∈ altImg K s, K.U j := by
  refine le_antisymm (le_iInf₂ fun j hj => ?_) (le_iInf fun k => biInf_le _
    (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hj
  exact iInf_le _ k

theorem altImg_altFace {i : ℕ} (s : K.Idx (i + 1))
    (j : Fin (i + 2)) :
    altImg K (K.face s j)
      = (altImg K s).erase (s.1 j) := by
  ext x
  simp only [altImg, Scheme.OrderedAffineCoverOf.face, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_erase, Function.comp_apply]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨s.2.injective.ne (Fin.succAbove_ne j k), Fin.succAbove j k, rfl⟩
  · rintro ⟨hne, k, rfl⟩
    obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg s.1 h))
    exact ⟨k', rfl⟩

/-- The ordered Čech index obtained by enumerating a finite set of chart indices. -/
def altOfFinset {i : ℕ} (T : Finset K.ι) (hT : T.card = i + 1) :
    K.Idx i :=
  ⟨T.orderEmbOfFin hT, (T.orderEmbOfFin hT).strictMono⟩

theorem altImg_altOfFinset {i : ℕ} (T : Finset K.ι) (hT : T.card = i + 1) :
    altImg K (altOfFinset K T hT) = T :=
  Finset.image_orderEmbOfFin_univ T hT

theorem altImg_deg0 (σ : K.Idx 0) :
    altImg K σ = {σ.1 0} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ 0), fun x hx => ?_⟩
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx; rw [← hj, Fin.fin_one_eq_zero j]

/-- The position of a chart index in an ordered Čech index. -/
def altPos {i : ℕ} (s : K.Idx i) (j : K.ι)
    (hj : j ∈ altImg K s) : Fin (i + 1) :=
  ((altImg K s).orderIsoOfFin (card_altImg K s)).symm ⟨j, hj⟩

theorem altIdx_val_altPos {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∈ altImg K s) :
    s.1 (altPos K s j hj) = j := by
  rw [altIdx_canonical K s, ← Finset.coe_orderIsoOfFin_apply,
    altPos, OrderIso.apply_symm_apply]

theorem altPos_val {i : ℕ} (s : K.Idx i) (p : Fin (i + 1)) :
    altPos K s (s.1 p) (Finset.mem_image_of_mem _ (Finset.mem_univ p)) = p :=
  s.2.injective (altIdx_val_altPos K s (s.1 p) _)

/-- The ordered Čech index obtained by inserting a new chart index. -/
def altInsert {i : ℕ} (s : K.Idx i) (j : K.ι)
    (hj : j ∉ altImg K s) : K.Idx (i + 1) :=
  altOfFinset K (insert j (altImg K s))
    (by rw [Finset.card_insert_of_notMem hj, card_altImg])

theorem altImg_altInsert {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∉ altImg K s) :
    altImg K (altInsert K s j hj)
      = insert j (altImg K s) :=
  altImg_altOfFinset K _ _

/-- The position occupied by the inserted chart index. -/
def insPos {i : ℕ} (s : K.Idx i) (j : K.ι)
    (hj : j ∉ altImg K s) : Fin (i + 2) :=
  altPos K (altInsert K s j hj) j
    (by rw [altImg_altInsert]; exact Finset.mem_insert_self j _)

theorem altInsert_val_insPos {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∉ altImg K s) :
    (altInsert K s j hj).1 (insPos K s j hj) = j :=
  altIdx_val_altPos K _ j _

theorem altFace_altInsert_insPos {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∉ altImg K s) :
    K.face (altInsert K s j hj)
      (insPos K s j hj) = s := by
  apply altIdx_eq_of_altImg
  rw [altImg_altFace, altInsert_val_insPos,
    altImg_altInsert, Finset.erase_insert hj]

theorem altPos_congr {i : ℕ} {s t : K.Idx i}
    (h : s = t) (j : K.ι) (hjs : j ∈ altImg K s)
    (hjt : j ∈ altImg K t) :
    altPos K s j hjs = altPos K t j hjt := by
  subst h; rfl

theorem altInsert_altFace_altPos {i : ℕ} (σ : K.Idx (i + 1))
    (j : K.ι) (hj : j ∈ altImg K σ)
    (hjp : j ∉ altImg K
      (K.face σ (altPos K σ j hj))) :
    altInsert K (K.face σ (altPos K σ j hj))
      j hjp = σ := by
  apply altIdx_eq_of_altImg
  rw [altImg_altInsert, altImg_altFace,
    altIdx_val_altPos, Finset.insert_erase hj]

theorem insPos_altFace_altPos {i : ℕ} (σ : K.Idx (i + 1))
    (j : K.ι) (hj : j ∈ altImg K σ)
    (hjp : j ∉ altImg K
      (K.face σ (altPos K σ j hj))) :
    insPos K (K.face σ (altPos K σ j hj)) j hjp
      = altPos K σ j hj := by
  unfold insPos
  exact altPos_congr K
    (altInsert_altFace_altPos K σ j hj hjp) j _ hj

theorem altFace_altInsert_ne {i : ℕ} (s : K.Idx (i + 1))
    (j : K.ι) (hj : j ∉ altImg K s)
    (k : Fin (i + 3)) (hk : k ≠ insPos K s j hj) :
    ∃ (p : Fin (i + 2)) (hjp : j ∉ altImg K (K.face s p)),
      K.face (altInsert K s j hj) k
        = altInsert K (K.face s p) j hjp
      ∧ (altInsert K s j hj).1 k = s.1 p := by
  set m := (altInsert K s j hj).1 k with hm_def
  have hmne : m ≠ j := fun heq => hk ((altInsert K s j hj).2.injective
    (heq.trans (altInsert_val_insPos K s j hj).symm))
  have hmem : m ∈ altImg K s := by
    have : m ∈ altImg K (altInsert K s j hj) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ k)
    rw [altImg_altInsert] at this
    exact (Finset.mem_insert.mp this).resolve_left hmne
  refine ⟨altPos K s m hmem, ?_, ?_, ?_⟩
  · rw [altImg_altFace, altIdx_val_altPos]
    exact fun h => hj (Finset.mem_of_mem_erase h)
  · apply altIdx_eq_of_altImg
    rw [altImg_altFace, altImg_altInsert,
      altImg_altInsert, altImg_altFace,
      altIdx_val_altPos, Finset.erase_insert_of_ne hmne.symm]
  · exact (altIdx_val_altPos K s m hmem).symm

end Scheme.OrderedAffineCoverOf

namespace Scheme.OrderedAffineCover

/-- Regard an ordered affine cover of the scheme as a cover of its top open. -/
def toCoverOf (K : V.OrderedAffineCover) : V.OrderedAffineCoverOf ⊤ where
  ι := K.ι
  U := K.U
  isAffineOpen := K.isAffineOpen
  le _ := le_top
  iSup_eq := K.iSup_eq_top

@[simp] theorem toCoverOf_U (K : V.OrderedAffineCover) (i : K.ι) : K.toCoverOf.U i = K.U i := rfl

/-- Intersect an ordered affine cover with an affine open in a separated scheme over the base. -/
def restrict (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) : V.OrderedAffineCoverOf W where
  ι := K.ι
  U i := K.U i ⊓ W
  isAffineOpen i := isAffineOpen_inf_of_isSeparated π (K.isAffineOpen i) hW
  le _ := inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K.iSup_eq_top, top_inf_eq]

@[simp] theorem restrict_U (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W
    : V.Opens}
    (hW : IsAffineOpen W) (i : K.ι) : (K.restrict π hW).U i = K.U i ⊓ W := rfl

end Scheme.OrderedAffineCover

namespace Scheme.OrderedAffineCoverOf

variable (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W)

/-- The base-ring module structure on sections supplied by the structural morphism. -/
@[reducible] def moduleSections : ∀ O : V.Opens, Module R Γ(V, O) :=
  fun O => (Scheme.TwoAffineOpenCover.algebraOfHom π O).toModule

/-- Cech cochains of the structure sheaf on the selected intersections of the cover. -/
abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, Γ(V, K.inter s)

/-- The base-linear restriction map on structure-sheaf sections. -/
def res {O O' : V.Opens} (h : O ≤ O') :
    letI := moduleSections π
    (Γ(V, O') : Type u) →ₗ[R] (Γ(V, O) : Type u) :=
  (OModulePresheaf.unit π).res h

theorem res_apply {O O' : V.Opens} (h : O ≤ O') (x : Γ(V, O')) :
    res π h x = (V.presheaf.map (homOfLE h).op).hom x := rfl

/-- The alternating sum of face restriction maps defining the Cech differential. -/
def d (i : ℕ) :
    letI := moduleSections π
    K.cochain i →ₗ[R] K.cochain (i + 1) :=
  letI := moduleSections π
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((res π (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (f : K.cochain i) (s : K.Idx (i + 1)) :
    letI := moduleSections π
    K.d π i f s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (V.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (f (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, res_apply]

/-- The augmentation sending a section on the covered open to its restrictions on the cover. -/
def aug :
    letI := moduleSections π
    (Γ(V, W) : Type u) →ₗ[R] K.cochain 0 :=
  letI := moduleSections π
  LinearMap.pi fun s => res π (K.inter_le_base s)

theorem aug_apply (w : Γ(V, W)) (s : K.Idx 0) :
    letI := moduleSections π
    K.aug π w s = (V.presheaf.map (homOfLE (K.inter_le_base s)).op).hom w := rfl

/-- The degree-zero Cech cohomology, represented by the kernel of the first differential. -/
abbrev H0 : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π 0)

/-- Positive Cech cohomology as cocycles modulo the image of the preceding differential. -/
abbrev HSucc (i : ℕ) : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π (i + 1)) ⧸ (LinearMap.range (K.d π i)).comap (LinearMap.ker (K.d π (i +
      1))).subtype

end Scheme.OrderedAffineCoverOf

theorem Scheme.OrderedAffineCover.d_toCoverOf (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)
    (i : ℕ) :
    K.toCoverOf.d π i = (OModulePresheaf.unit π).d K i := rfl

end AlgebraicGeometry

end
