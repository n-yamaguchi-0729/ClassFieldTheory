/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective.lean
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
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Tactic.Ext
import Mathlib.Tactic.TermCongr
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic.Choose

/-!
# Epimorphisms and locally surjective module maps

A morphism of module sheaves is an epimorphism precisely when sections locally lift
through its components.
-/

section Hom_epi_iff_locallySurjective

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_epi_iff_locallySurjective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

universe v v' u'

namespace SheafOfModules
open _root_.SheafOfModules
open _root_.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem epi_toSheaf_map_of_epi {M N : SheafOfModules.{v} R} (φ : M ⟶ N) [Epi φ] :
    Epi ((toSheaf R).map φ) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
  let G := SheafOfModules.forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let S := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  let ψ := G.map φ
  have hcounit : IsIso adj.counit :=
    inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).counit)
  let εM : S.obj (G.obj M) ≅ M :=
    @asIso _ _ _ _ (adj.counit.app M) (NatIso.isIso_app_of_isIso adj.counit M)
  let εN : S.obj (G.obj N) ≅ N :=
    @asIso _ _ _ _ (adj.counit.app N) (NatIso.isIso_app_of_isIso adj.counit N)
  have hnat : S.map ψ ≫ εN.hom = εM.hom ≫ φ := adj.counit.naturality φ
  have : Epi (S.map ψ) := by
    have : S.map ψ = (εM.hom ≫ φ) ≫ εN.inv := (Iso.eq_comp_inv εN).2 hnat
    rw [this]; infer_instance
  have h0 : S.map (cokernel.π ψ) = 0 := by
    apply zero_of_epi_comp (S.map ψ)
    rw [← S.map_comp, cokernel.condition]
    exact S.map_zero _ _
  let T := PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v}
  have hT : ∀ {P Q : PresheafOfModules.{v} R.obj} (f : P ⟶ Q),
      T.map f = (toSheaf R).map (S.map f) := fun f => rfl
  have h0' : T.map (cokernel.π ψ) = 0 := by
    rw [hT, h0]
    exact Functor.map_zero _ _ _
  have hc := isColimitOfHasCokernelOfPreservesColimit T ψ
  have hTψ : Epi (T.map ψ) := by
    refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc g hg
    rw [← hd]
    change T.map (cokernel.π ψ) ≫ d = 0
    rw [h0', zero_comp]
  have h2 : T.map ψ ≫ ((toSheaf R).mapIso εN).hom =
      ((toSheaf R).mapIso εM).hom ≫ (toSheaf R).map φ := by
    change (toSheaf R).map (S.map ψ) ≫ (toSheaf R).map εN.hom =
      (toSheaf R).map εM.hom ≫ (toSheaf R).map φ
    rw [← Functor.map_comp, ← Functor.map_comp, hnat]
  have : (toSheaf R).map φ =
      ((toSheaf R).mapIso εM).inv ≫ T.map ψ ≫ ((toSheaf R).mapIso εN).hom :=
    (Iso.eq_inv_comp _).2 h2.symm
  rw [this]
  have : IsIso ((toSheaf R).mapIso εN).hom := ((toSheaf R).mapIso εN).isIso_hom
  have hN : Epi ((toSheaf R).mapIso εN).hom :=
    IsIso.epi_of_iso ((toSheaf R).mapIso εN).hom
  have : IsIso ((toSheaf R).mapIso εM).inv := ((toSheaf R).mapIso εM).isIso_inv
  have hM : Epi ((toSheaf R).mapIso εM).inv :=
    IsIso.epi_of_iso ((toSheaf R).mapIso εM).inv
  have h1 : Epi (T.map ψ ≫ ((toSheaf R).mapIso εN).hom) :=
    @epi_comp _ _ _ _ _ (T.map ψ) hTψ _ hN
  exact @epi_comp _ _ _ _ _ _ hM _ h1

end SheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective {M N : X.Modules} (φ :
  M ⟶ N) :
    Epi φ ↔ ∀ (U : X.Opens) (s : Γ(N, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ N.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V) := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have key : Epi φ ↔ Sheaf.IsLocallySurjective (F.map φ) := by
    constructor
    · intro hφ
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ :=
        ⟨fun g h w => (cancel_epi φ).1 w⟩
      have : Epi (F.map φ) :=
        @SheafOfModules.epi_toSheaf_map_of_epi _ _ _ X.ringCatSheaf _ _ M N φ hepi
      exact (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) (φ := F.map φ)).2
          inferInstance
    · intro h
      have : Epi (F.map φ) := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) (φ :=
          F.map φ)).1 h
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ := F.epi_of_epi_map inferInstance
      exact ⟨fun g h w => (@cancel_epi _ _ _ _ _ φ hepi _ _).1 w⟩
  rw [key]
  constructor
  · intro h U s x hx
    obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (F.map φ).hom (U := op U) s x hx
    exact ⟨V, i.le, hxV, t, ht⟩
  · intro h
    refine ⟨fun {U} s x hx => ?_⟩
    obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
    exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩


end AlgebraicGeometry.Scheme.Modules
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_epi_iff_locallySurjective
end ProofImplementation

end Hom_epi_iff_locallySurjective

section Hom_mono_iff_injective

/-!
# Monomorphisms of module sheaves

Characterizes monomorphisms of scheme modules by injectivity on sections.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_mono_iff_injective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.mono_iff_injective
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    Mono φ ↔ ∀ U : X.Opens, Function.Injective (φ.app U) := by
  constructor
  · intro hφ U
    let ev : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} := (CategoryTheory.evaluation _ Ab.{u}).obj (op U)
    have : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
      preserves_mono_of_preservesLimit (Scheme.Modules.toPresheaf X) φ
    have : PreservesLimitsOfShape WalkingCospan ev := evaluation_preservesLimitsOfShape _
    have : Mono (ev.map ((Scheme.Modules.toPresheaf X).map φ)) :=
      preserves_mono_of_preservesLimit _ _
    have h : Mono (φ.app U) := this
    exact (AddCommGrpCat.mono_iff_injective (φ.app U)).1 h
  · intro h
    refine ⟨fun g g' w => ?_⟩
    refine Scheme.Modules.hom_ext g g' fun U => ?_
    ext x
    apply h U
    have := congr(($w).app U x)
    simpa [Scheme.Modules.Hom.comp_app] using this
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_mono_iff_injective
end ProofImplementation

end Hom_mono_iff_injective

section Hom_isIso_of_isIso_app_of_iSup_eq_top

/-!
# Detecting module isomorphisms on an open cover

A morphism is an isomorphism if its components are isomorphisms on opens contained
in the members of a cover.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top {X :
  Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {ι : Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → IsIso (φ.app V)) : IsIso φ := by
  have cover : ∀ x : X, ∃ i, x ∈ U i := fun x ↦
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial)
  let F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨M.presheaf, M.isSheaf⟩
  let G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  have : (Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat.{u}) :=
    inferInstance
  have hψ : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨?_, ?_⟩
    · refine ⟨fun {W} x y hxy p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W.unop ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W.unop ⊓ U i) inf_le_right
      apply (ConcreteCategory.bijective_of_isIso (φ.app (W.unop ⊓ U i))).1
      change φ.mapPresheaf.app _ (M.presheaf.map _ x) = φ.mapPresheaf.app _ (M.presheaf.map _ y)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg _ hxy
    · refine ⟨fun {W} s p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W ⊓ U i) inf_le_right
      obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (φ.app (W ⊓ U i))).2
        (N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op s)
      exact ⟨t, ht⟩
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  have : IsIso ((sheafToPresheaf _ _).map ψ) := inferInstance
  have : IsIso (ψ.hom.app (Opposite.op V)) := by
    change IsIso (((sheafToPresheaf _ _).map ψ).app (Opposite.op V))
    infer_instance
  exact this
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
end ProofImplementation

end Hom_isIso_of_isIso_app_of_iSup_eq_top

section isZero_of_forall_exists_isZero_pullback_obj

/-!
# Vanishing of modules detected by pullback

Detects a zero module from vanishing pullbacks on a family covering all points.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

lemma sections_eq_zero_of_isZero_pullback_ι {M : X.Modules} (U : X.Opens)
    (hU : IsZero ((Scheme.Modules.pullback U.ι).obj M)) (W : X.Opens) (hWU : W ≤ U)
    (s : Γ(M, W)) : s = 0 := by
  have h1 : IsZero ((restrictFunctor U.ι).obj M) :=
    hU.of_iso ((restrictFunctorIsoPullback U.ι).app M)
  have h2 : (𝟙 ((restrictFunctor U.ι).obj M) :) = 0 := h1.eq_of_src _ _
  have h4 : ∀ t : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)), t = 0 := fun t => by
    have h3 := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ (U.ι ⁻¹ᵁ W) : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ
      W)) → _) t) h2
    simp only [_root_.AlgebraicGeometry.Scheme.Modules.Hom.id_app,
      _root_.AlgebraicGeometry.Scheme.Modules.Hom.zero_app] at h3
    exact h3
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  let i : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⟶ W := homOfLE e.le
  let j : W ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := homOfLE e.ge
  have hij : j ≫ i = 𝟙 W := Subsingleton.elim _ _
  calc s = M.presheaf.map (𝟙 (op W)) s := by rw [M.presheaf.map_id]; rfl
    _ = M.presheaf.map (j ≫ i).op s := by rw [hij]; rfl
    _ = M.presheaf.map j.op (M.presheaf.map i.op s) := by
      rw [op_comp, M.presheaf.map_comp]; rfl
    _ = 0 := by rw [h4 (M.presheaf.map i.op s), map_zero]

theorem _root_.AlgebraicGeometry.Scheme.Modules.isZero_of_forall_exists_isZero_pullback_obj (M :
  X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsZero ((Scheme.Modules.pullback U.ι).obj M)) :
    IsZero M := by
  choose U hxU hU using h
  have hsec : ∀ (W : X.Opens) (s : Γ(M, W)), s = 0 := by
    intro W s
    let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
    let V : W → X.Opens := fun x => W ⊓ U x.1
    refine F.eq_of_locally_eq' V W (fun x => homOfLE inf_le_left)
      (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx, hxU x⟩) s 0 fun x => ?_
    rw [map_zero]
    exact sections_eq_zero_of_isZero_pullback_ι (U x.1) (hU x.1) (W ⊓ U x.1) inf_le_right _
  rw [IsZero.iff_id_eq_zero]
  ext W s
  change s = 0
  exact hsec W s


end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end isZero_of_forall_exists_isZero_pullback_obj

section Hom_isIso_of_forall_exists_isIso_pullback_map

/-!
# Detecting isomorphisms by local pullback

A module morphism is an isomorphism when its pullback is an isomorphism
on an open neighborhood of each point.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

lemma restrictFunctor_map_app' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (W : (U : Scheme.{u}).Opens) :
    ((restrictFunctor U.ι).map φ).app W = φ.app (U.ι ''ᵁ W) := rfl

lemma isIso_app_of_isIso_pullback_ι_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (hU : IsIso ((Scheme.Modules.pullback U.ι).map φ)) (W : X.Opens) (hWU : W ≤ U) :
    IsIso (φ.app W) := by
  have h1 : IsIso ((restrictFunctor U.ι).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι) φ).2 hU
  have h2 := Hom.isIso_iff_isIso_app.1 h1 (U.ι ⁻¹ᵁ W)
  rw [restrictFunctor_map_app'] at h2
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  rw [← e]
  exact h2

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map {M N :
  X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso φ := by
  choose U hxU hU using h
  refine Hom.isIso_of_isIso_app_of_iSup_eq_top φ U ?_ (fun x V hV => ?_)
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  · exact isIso_app_of_isIso_pullback_ι_map φ (U x) (hU x) V hV


end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end Hom_isIso_of_forall_exists_isIso_pullback_map
