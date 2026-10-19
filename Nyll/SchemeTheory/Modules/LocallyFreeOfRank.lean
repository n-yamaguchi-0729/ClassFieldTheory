/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Scheme modules locally free of a fixed rank

Defines local freeness by trivializations on neighborhoods of every point.
-/

section LocallyFreeOfRank

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A module that is locally isomorphic to a free sheaf with n generators. -/
structure IsLocallyFreeOfRank (n : ℕ) (M : X.Modules) : Prop where
  /-- Every point has an open neighborhood on which the module is free of rank n. -/
  exists_trivialization : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)))

end AlgebraicGeometry.Scheme.Modules

end LocallyFreeOfRank

section IsLocallyFreeOfRank_of_iso

/-!
# Local freeness preserved by isomorphisms

Transfers local freeness of a fixed rank along an isomorphism of scheme modules.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_of_iso

universe u
open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_iso {X : Scheme.{u}} {n :
  ℕ} {M N : X.Modules} (e : M ≅ N) (h : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsLocallyFreeOfRank n N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨i⟩⟩ := h.exists_trivialization x
  exact ⟨U, hx, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ i⟩⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_of_iso
end ProofImplementation

end IsLocallyFreeOfRank_of_iso

section IsLocallyFreeOfRank_pullback

/-!
# Pullback preserves local freeness and rank

Pullback transports local trivializations through the canonical pullback comparison
for free module sheaves.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_pullback

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

scoped instance opensMap_final_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

/-- The canonical identification of the pullback of a free module sheaf with the same free module
  sheaf. -/
noncomputable def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

namespace IsLocallyFreeOfRank
open _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank
end IsLocallyFreeOfRank
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank in
theorem IsLocallyFreeOfRank.pullback' {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : IsLocallyFreeOfRank n E) :
    IsLocallyFreeOfRank n ((Modules.pullback ψ).obj E) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, ⟨eU⟩⟩ := hE.exists_trivialization (ψ.base x)
  refine ⟨ψ ⁻¹ᵁ U, hU, ⟨?_⟩⟩
  have hfact : (ψ ⁻¹ᵁ U).ι ≫ ψ = (ψ ∣_ U) ≫ U.ι := (morphismRestrict_ι ψ U).symm
  exact (Modules.pullbackComp _ _).app E ≪≫ (Modules.pullbackCongr hfact).app E ≪≫
    ((Modules.pullbackComp _ _).app E).symm ≪≫ (Modules.pullback (ψ ∣_ U)).mapIso eU ≪≫
    pullbackFreeIso (ψ ∣_ U) (ULift.{u} (Fin n))

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback ψ).obj E) :=
  AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback' ψ hE
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_pullback
end ProofImplementation

end IsLocallyFreeOfRank_pullback

section IsLocallyFreeOfRank_of_forall_exists_opens

/-!
# Local freeness from an open cover

Pullback to open subschemes identifies the local trivializations used to establish a fixed rank.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens

universe u
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens {X :
  Scheme.{u}} {n : ℕ} {M : X.Modules}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback U.ι).obj M)) :
    Scheme.Modules.IsLocallyFreeOfRank n M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hU.exists_trivialization ⟨x, hxU⟩
  refine ⟨U.ι ''ᵁ V, ⟨⟨x, hxU⟩, hxV, rfl⟩, ⟨?_⟩⟩
  let i := U.ι.isoImage V
  have hi : i.inv ≫ V.ι ≫ U.ι = (U.ι ''ᵁ V).ι := U.ι.isoImage_inv_ι V
  exact (pullbackCongr hi.symm).app M ≪≫
    ((pullbackComp i.inv (V.ι ≫ U.ι)).symm.app M) ≪≫
    (Scheme.Modules.pullback i.inv).mapIso
      (((pullbackComp V.ι U.ι).symm.app M) ≪≫ (Scheme.Modules.pullback V.ι).mapIso (Iso.refl _) ≪≫
          e) ≪≫
    pullbackFreeIso i.inv _
end Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end IsLocallyFreeOfRank_of_forall_exists_opens
