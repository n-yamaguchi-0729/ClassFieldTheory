/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Conv
import Nyll.SchemeTheory.Modules.Tensor.TensorSections

/-!
# Local bijectivity of multiplication by a section

Multiplication by a fixed global section is bijective on every open when it is bijective
on a suitable neighbourhood of each point.
-/

section FrameLocality

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FrameLocalSol

variable {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤))

/-- The restriction of the fixed global section `σ` to the open subset `W`. -/
noncomputable abbrev res (W : X.Opens) : Γ(M, W) := M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ

theorem res_map {W W' : X.Opens} (i : W' ⟶ W) : M.presheaf.map i.op (res M σ W) = res M σ W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem smul_res {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) :
    M.presheaf.map i.op (g • res M σ W) = X.presheaf.map i.op g • res M σ W' := by
  rw [Scheme.Modules.map_smul, res_map]

/-- The sheaf of abelian groups underlying the module sheaf `M`. -/
noncomputable def abSheaf : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem main (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • res M σ W) :
    Function.Bijective fun g : Γ(X, V) => g • res M σ V := by
  classical
  choose U hxU hU using fun x : V => h x.1 x.2
  let W : V → X.Opens := fun x => V ⊓ U x
  have hWV : ∀ x, W x ≤ V := fun x => inf_le_left
  have hWU : ∀ x, W x ≤ U x := fun x => inf_le_right
  have hcover : V ≤ iSup W := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, ⟨hy, hxU ⟨y, hy⟩⟩⟩
  constructor
  · intro g₁ g₂ hg
    have hg' : g₁ • res M σ V = g₂ • res M σ V := hg
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf W V (fun x => homOfLE (hWV x)) hcover
    intro x
    apply (hU x (W x) (hWU x)).1
    change X.presheaf.map (homOfLE (hWV x)).op g₁ • res M σ (W x) =
      X.presheaf.map (homOfLE (hWV x)).op g₂ • res M σ (W x)
    rw [← smul_res, ← smul_res, hg']
  · intro s
    have hloc : ∀ x, ∃! g : Γ(X, W x), g • res M σ (W x) = M.presheaf.map (homOfLE (hWV x)).op s :=
      fun x => (Function.bijective_iff_existsUnique _).1 (hU x (W x) (hWU x)) _
    choose gx hgx hgx_uniq using hloc
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W gx := by
      intro x y
      apply (hU x (W x ⊓ W y) (inf_le_left.trans (hWU x))).1
      change X.presheaf.map (Opens.infLELeft (W x) (W y)).op (gx x) • res M σ (W x ⊓ W y) =
        X.presheaf.map (Opens.infLERight (W x) (W y)).op (gx y) • res M σ (W x ⊓ W y)
      rw [← smul_res M σ (Opens.infLELeft (W x) (W y)), hgx x, ← smul_res M σ (Opens.infLERight
          (W x) (W y)),
        hgx y, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, ← op_comp, ← op_comp]
      rfl
    obtain ⟨g, hg, -⟩ : ∃! g : Γ(X, V), ∀ x, X.presheaf.map (homOfLE (hWV x)).op g = gx x :=
      TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun x => homOfLE (hWV x)) hcover gx hcompat
    refine ⟨g, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (abSheaf M) W V (fun x => homOfLE (hWV x)) hcover
    intro x
    change M.presheaf.map (homOfLE (hWV x)).op (g • res M σ V) = M.presheaf.map (homOfLE (hWV
        x)).op s
    rw [smul_res, ← hgx x]
    exact congrArg (· • res M σ (W x)) (hg x)

end FrameLocalSol

theorem _root_.AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul
    {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ
          : Γ(M, W))) :
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ :
        Γ(M, V)) :=
  FrameLocalSol.main M σ V h
end Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end FrameLocality

section IsFrameOn_of_iSup

/-!
# Scheme Modules Is Frame On of i Sup
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_of_iSup

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace FrameL1Aux
variable {X : Scheme.{u}} {M : X.Modules}
theorem map_map {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

end FrameL1Aux

open AlgebraicGeometry.Scheme.Modules FrameL1Aux in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {ι : Type v} {s : Γ(M, U)}
    (V : ι → X.Opens) (h : ∀ i, Scheme.Modules.IsFrameOn s (V i)) :
    Scheme.Modules.IsFrameOn s (⨆ i, V i) := by
  intro W hWU hWV
  let Wi : ι → X.Opens := fun i => W ⊓ V i
  have hcov : W ≤ ⨆ i, Wi i := by
    intro x hx
    have hx' : x ∈ (⨆ i, V i : X.Opens) := hWV hx
    rw [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, ⟨hx, hi⟩⟩
  let FM : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩
  set sW : Γ(M, W) := M.presheaf.map (homOfLE hWU).op s with hsW
  have key : ∀ i, Function.Bijective fun g : Γ(X, Wi i) =>
      g • (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW : Γ(M, Wi i)) := by
    intro i
    have := h i (W := Wi i) (inf_le_left.trans hWU) inf_le_right
    rw [hsW, map_map]
    exact this
  constructor
  · intro g g' hgg'
    simp only at hgg'
    apply X.sheaf.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcov
    intro i
    apply (key i).1
    change X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op g • _ =
      X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op g' • _
    rw [← M.map_smul, ← M.map_smul]
    exact congrArg _ hgg'
  · intro x
    have hloc : ∀ i, ∃! g : Γ(X, Wi i),
        g • (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW : Γ(M, Wi i)) =
          M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op x :=
      fun i => (Function.bijective_iff_existsUnique _).1 (key i) _
    choose g hg hguniq using hloc
    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 Wi g := by
      intro i j
      have hb := h i (W := Wi i ⊓ Wi j) ((inf_le_left.trans inf_le_left).trans hWU)
        (inf_le_left.trans inf_le_right)
      apply hb.1
      simp only
      have e1 : M.presheaf.map (homOfLE ((inf_le_left.trans inf_le_left).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_left : Wi i ⊓ Wi j ≤ Wi i)).op
            (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW) := by
        rw [hsW, map_map, map_map]
      have e2 : M.presheaf.map (homOfLE ((inf_le_left.trans inf_le_left).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_right : Wi i ⊓ Wi j ≤ Wi j)).op
            (M.presheaf.map (homOfLE (inf_le_left : Wi j ≤ W)).op sW) := by
        rw [hsW, map_map, map_map]
      conv_lhs => rw [e1]
      conv_rhs => rw [e2]
      change X.presheaf.map (homOfLE inf_le_left).op (g i) • _ =
        X.presheaf.map (homOfLE inf_le_right).op (g j) • _
      rw [← M.map_smul, ← M.map_smul, hg i, hg j, map_map, map_map]
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' Wi W (fun i => homOfLE inf_le_left) hcov g
      hcomp
    let G' : Γ(X, W) := G
    refine ⟨G', ?_⟩
    simp only
    apply FM.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcov
    intro i
    change M.presheaf.map (homOfLE inf_le_left).op (G' • sW) = M.presheaf.map (homOfLE
      inf_le_left).op x
    rw [M.map_smul]
    have : X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op G' = g i := hG i
    rw [this, hg i]
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_of_iSup
end ProofImplementation

end IsFrameOn_of_iSup

section IsFrameOn_exists_isUnit_smul_eq

/-!
# Scheme Modules Is Frame On exists is Unit smul eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {s s' : Γ(M, U)} {V : X.Opens}
    (hs : Scheme.Modules.IsFrameOn s V) (hs' : Scheme.Modules.IsFrameOn s' V)
    {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    ∃ u : Γ(X, W), IsUnit u ∧
      u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU).op s' := by
  obtain ⟨u, hu⟩ := (hs hWU hWV).2 (M.presheaf.map (homOfLE hWU).op s')
  obtain ⟨w, hw⟩ := (hs' hWU hWV).2 (M.presheaf.map (homOfLE hWU).op s)
  refine ⟨u, ?_, hu⟩
  have h1 : (w * u) • M.presheaf.map (homOfLE hWU).op s =
      (1 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s := by
    rw [mul_smul, one_smul]
    simp only at hu hw
    rw [hu, hw]
  have hwu : w * u = 1 := (hs hWU hWV).1 h1
  exact ⟨⟨u, w, (mul_comm u w).trans hwu, hwu⟩, rfl⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq
end ProofImplementation

end IsFrameOn_exists_isUnit_smul_eq

section isIso_of_isFrameOn_of_iSup_eq_top

/-!
# Scheme Modules is Iso of is Frame On of i Sup eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace N2P4

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {P Q : X.Modules}

theorem map_map (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M,
  V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem app_map (μ : P ⟶ Q) {V W : X.Opens} (h : W ≤ V) (x : Γ(P, V)) :
    μ.app W (P.presheaf.map (homOfLE h).op x) = Q.presheaf.map (homOfLE h).op (μ.app V x) := by
  have := (μ.mapPresheaf).naturality (homOfLE h).op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(P, V) → Γ(Q, W))) this) x

theorem app_injective_of_le (μ : P ⟶ Q) {V : X.Opens} (p : Γ(P, V)) (q : Γ(Q, V))
    (hp : IsFrameOn p V) (hq : IsFrameOn q V) (hμ : μ.app V p = q) {W : X.Opens} (hW : W ≤ V) :
    Function.Injective (μ.app W) := by
  intro x x' hxx'
  obtain ⟨g, rfl⟩ := (hp hW hW).2 x
  obtain ⟨g', rfl⟩ := (hp hW hW).2 x'
  simp only [Scheme.Modules.Hom.app_smul, app_map, hμ] at hxx'
  have := (hq hW hW).1 hxx'
  rw [this]

theorem isIso_of_frames (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  let Wi : ι → X.Opens := fun i => W ⊓ 𝒱 i
  have hcovW : W ≤ ⨆ i, Wi i := by
    intro x hx
    have hx' : x ∈ (⨆ i, 𝒱 i : X.Opens) := by rw [hcov]; trivial
    rw [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, ⟨hx, hi⟩⟩
  let FP : TopCat.Sheaf Ab X.carrier := ⟨P.presheaf, P.isSheaf⟩
  let FQ : TopCat.Sheaf Ab X.carrier := ⟨Q.presheaf, Q.isSheaf⟩
  have hinjW : ∀ {W' : X.Opens} (i : ι), W' ≤ 𝒱 i → Function.Injective (μ.app W') :=
    fun i h => app_injective_of_le μ (p i) (q i) (hp i) (hq i) (hμ i) h
  constructor
  · intro x x' h
    apply FP.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcovW
    intro i
    apply hinjW i inf_le_right
    change μ.app (Wi i) (P.presheaf.map (homOfLE inf_le_left).op x) =
      μ.app (Wi i) (P.presheaf.map (homOfLE inf_le_left).op x')
    rw [app_map, app_map]
    exact congrArg _ h
  · intro y
    have hloc : ∀ i, ∃ x : Γ(P, Wi i), μ.app (Wi i) x = Q.presheaf.map (homOfLE inf_le_left).op y
      := by
      intro i
      obtain ⟨g, hg⟩ := (hq i (inf_le_right : Wi i ≤ 𝒱 i) inf_le_right).2
        (Q.presheaf.map (homOfLE inf_le_left).op y)
      refine ⟨g • P.presheaf.map (homOfLE (inf_le_right : Wi i ≤ 𝒱 i)).op (p i), ?_⟩
      rw [Scheme.Modules.Hom.app_smul, app_map, hμ i]
      exact hg
    choose x hx using hloc
    have hcomp : TopCat.Presheaf.IsCompatible FP.1 Wi x := by
      intro i j
      apply hinjW i (inf_le_left.trans inf_le_right)
      change μ.app (Wi i ⊓ Wi j) (P.presheaf.map (homOfLE inf_le_left).op (x i)) =
        μ.app (Wi i ⊓ Wi j) (P.presheaf.map (homOfLE inf_le_right).op (x j))
      rw [app_map, app_map, hx i, hx j, map_map, map_map]
    obtain ⟨s, hs, -⟩ := FP.existsUnique_gluing' Wi W (fun i => homOfLE inf_le_left) hcovW x hcomp
    refine ⟨show Γ(P, W) from s, ?_⟩
    apply FQ.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcovW
    intro i
    change Q.presheaf.map (homOfLE inf_le_left).op (μ.app W s) = Q.presheaf.map (homOfLE
      inf_le_left).op y
    rw [← app_map, ← hx i]
    exact congrArg _ (hs i)

end N2P4

open AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top {X : Scheme.{u}}
  {P Q : X.Modules} (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, Scheme.Modules.IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, Scheme.Modules.IsFrameOn (q i) (𝒱
      i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ :=
  N2P4.isIso_of_frames μ 𝒱 hcov p q hp hq hμ
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
end ProofImplementation

end isIso_of_isFrameOn_of_iSup_eq_top
