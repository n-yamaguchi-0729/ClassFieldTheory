/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Ext
import Mathlib.Tactic.TermCongr
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# Lifting kernel sections in an exact complex

When the first map is a monomorphism, a section killed by the second map comes from
a section under the first map.
-/

section exists_app_eq_of_exact_of_app_eq_zero

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero

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

scoped instance : (toPresheaf X).Additive where
  map_add := by intros; rfl

/-- Evaluate a presheaf of abelian groups on the open subset `U`. -/
noncomputable abbrev evalAt (U : X.Opens) : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} :=
  (CategoryTheory.evaluation _ Ab.{u}).obj (op U)

theorem exists_app_eq_of_exact_of_app_eq_zero (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m := by
  have hK : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
  have hK₁ := KernelFork.mapIsLimit _ hK (toPresheaf X)
  have hPL : PreservesLimitsOfShape WalkingParallelPair (evalAt (X := X) U) :=
    evaluation_preservesLimitsOfShape _
  have : (evalAt (X := X) U).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_evaluation_obj (op U)
  have hK' := KernelFork.mapIsLimit _ hK₁ (evalAt (X := X) U)
  let k : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ (evalAt (X := X) U).obj ((toPresheaf X).obj S.X₂) :=
    AddCommGrpCat.ofHom ((zmultiplesHom Γ(S.X₂, U) m).comp AddEquiv.ulift.toAddMonoidHom)
  have hk1 : k (ULift.up (1 : ℤ)) = m := by
    change (zmultiplesHom Γ(S.X₂, U) m) (1 : ℤ) = m
    rw [zmultiplesHom_apply, one_zsmul]
  have hk : k ≫ (evalAt (X := X) U).map ((toPresheaf X).map S.g) = 0 := by
    ext ⟨z⟩
    change (S.g.app U) ((zmultiplesHom Γ(S.X₂, U) m) z) = 0
    rw [zmultiplesHom_apply, map_zsmul, hm, smul_zero]
  refine ⟨(KernelFork.IsLimit.lift' hK' k hk).1 (ULift.up (1 : ℤ)), ?_⟩
  have h := (KernelFork.IsLimit.lift' hK' k hk).2
  have h' := congr($h (ULift.up (1 : ℤ)))
  rw [hk1] at h'
  exact h'

end AlgebraicGeometry.Scheme.Modules

open Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry.Scheme in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero {X :
  Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m :=
  Modules.exists_app_eq_of_exact_of_app_eq_zero
    S hS U m hm
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
end ProofImplementation

end exists_app_eq_of_exact_of_app_eq_zero

section shortExact_of_app_injective_of_locallySurjective_of_locallyExact

/-!
# Short exactness from sectionwise and local conditions

Sectionwise injectivity, local surjectivity, and local lifting of kernel sections
establish short exactness of a complex of module sheaves.
-/

section ProofImplementation

namespace AlgebraicGeometry.Scheme.Modules

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.Opposite _root_.TopologicalSpace

theorem shortExact_of_app_injective_of_locallySurjective_of_locallyExact
    {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hf : ∀ U : X.Opens, Function.Injective (S.f.app U))
    (hg : ∀ (U : X.Opens) (s : Γ(S.X₃, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₃.presheaf.map (homOfLE i).op s ∈ Set.range (S.g.app V))
    (hfg : ∀ (U : X.Opens) (m : Γ(S.X₂, U)), S.g.app U m = 0 → ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₂.presheaf.map (homOfLE i).op m ∈ Set.range (S.f.app V)) :
    S.ShortExact where
  mono_f := (Scheme.Modules.Hom.mono_iff_injective S.f).2 hf
  epi_g := (Scheme.Modules.Hom.epi_iff_locallySurjective S.g).2 hg
  exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift, Scheme.Modules.Hom.epi_iff_locallySurjective]
    intro U s x hx
    have hι : ∀ V : X.Opens, Function.Injective ((kernel.ι S.g).app V) :=
      (Scheme.Modules.Hom.mono_iff_injective _).1 inferInstance
    have h0 : S.g.app U ((kernel.ι S.g).app U s) = 0 := by
      change ((kernel.ι S.g).app U ≫ S.g.app U) s = 0
      rw [← Scheme.Modules.Hom.comp_app, kernel.condition, Scheme.Modules.Hom.zero_app]
      rfl
    obtain ⟨V, i, hxV, e, he⟩ := hfg U _ h0 x hx
    refine ⟨V, i, hxV, e, hι V ?_⟩
    have h1 : (kernel.ι S.g).app V ((kernel.lift S.g S.f S.zero).app V e) = S.f.app V e := by
      change ((kernel.lift S.g S.f S.zero).app V ≫ (kernel.ι S.g).app V) e = S.f.app V e
      rw [← Scheme.Modules.Hom.comp_app, kernel.lift_ι]
    have h2 : (kernel.ι S.g).app V ((kernel S.g).presheaf.map (homOfLE i).op s) =
        S.X₂.presheaf.map (homOfLE i).op ((kernel.ι S.g).app U s) := by
      have := congr($((kernel.ι S.g).mapPresheaf.naturality (homOfLE i).op) s)
      simpa using this
    rw [h1, h2, he]
end AlgebraicGeometry.Scheme.Modules
end ProofImplementation

end shortExact_of_app_injective_of_locallySurjective_of_locallyExact

section epi_sheafification_map_of_locallySurjective

/-!
# Epimorphisms induced by locally surjective presheaf maps

Sheafification turns a locally surjective morphism of module presheaves into an epimorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_epi_sheafification_map_of_locallySurjective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

universe v v' u'

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem epi_sheafification_map_of_isLocallySurjective {P Q : PresheafOfModules.{v} R₀}
    (ψ : P ⟶ Q) [Presheaf.IsLocallySurjective J ((toPresheaf R₀).map ψ)] :
    Epi ((sheafification.{v} α).map ψ) := by
  apply (SheafOfModules.toSheaf.{v} R).epi_of_epi_map
  change Epi ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ))
  let _ : Sheaf.IsLocallySurjective
      ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ))
    let _ : Presheaf.IsLocallySurjective J
        (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P) ≫
          CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ)) := by
      rw [← CategoryTheory.toSheafify_naturality]
      infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J
      (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P)) _
  infer_instance

end PresheafOfModules

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

theorem _root_.AlgebraicGeometry.Scheme.Modules.epi_sheafification_map_of_locallySurjective {P Q :
  X.PresheafOfModules} (ψ : P ⟶ Q)
    (h : ∀ (U : X.Opens) (s : Q.obj (op U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ Q.map (homOfLE i).op s ∈ Set.range (ψ.app (op V))) :
    Epi ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ψ) := by
  let _ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map ψ) :=
    ⟨fun {U} s x hx => by
      obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
      exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩⟩
  exact PresheafOfModules.epi_sheafification_map_of_isLocallySurjective (𝟙 X.ringCatSheaf.obj) ψ


end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_epi_sheafification_map_of_locallySurjective
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end epi_sheafification_map_of_locallySurjective

section shortExact_map_pushforward_of_forall_exists_surjective_app

/-!
# Short exactness after pushforward

Local surjectivity of the second map on inverse images of opens ensures that pushforward
preserves the short exact complex.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app

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
namespace PushSES
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X T : Scheme.{u}} (π : X ⟶ T) (S : ShortComplex X.Modules)

theorem g_app_eq (U : T.Opens) (m : Γ(S.X₂, π ⁻¹ᵁ U)) :
    (S.map (Scheme.Modules.pushforward π)).g.app U m = S.g.app (π ⁻¹ᵁ U) m := rfl

theorem f_app_eq (U : T.Opens) (m : Γ(S.X₁, π ⁻¹ᵁ U)) :
    (S.map (Scheme.Modules.pushforward π)).f.app U m = S.f.app (π ⁻¹ᵁ U) m := rfl

theorem shortExact (hS : S.ShortExact)
    (hsurj : ∀ (U : T.Opens), ∀ y ∈ U, ∃ V : T.Opens, y ∈ V ∧ V ≤ U ∧
      Function.Surjective (S.g.app (π ⁻¹ᵁ V))) :
    (S.map (Scheme.Modules.pushforward π)).ShortExact := by
  have := hS.mono_f
  refine Scheme.Modules.shortExact_of_app_injective_of_locallySurjective_of_locallyExact _ ?_ ?_ ?_
  · intro U
    exact (Scheme.Modules.Hom.mono_iff_injective S.f).mp hS.mono_f (π ⁻¹ᵁ U)
  · intro U s x hx
    obtain ⟨V, hxV, hVU, hV⟩ := hsurj U x hx
    obtain ⟨m, hm⟩ := hV (S.X₃.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U from fun _ h => hVU
        h)).op s)
    exact ⟨V, hVU, hxV, m, hm⟩
  · intro U m hm x hx
    obtain ⟨e, he⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact (π ⁻¹ᵁ U) m hm
    refine ⟨U, le_rfl, hx, e, ?_⟩
    change S.f.app (π ⁻¹ᵁ U) e = ((Scheme.Modules.pushforward π).obj S.X₂).presheaf.map (homOfLE
        le_rfl).op m
    have hid : ((Scheme.Modules.pushforward π).obj S.X₂).presheaf.map
        (homOfLE (le_refl U)).op = 𝟙 _ := by
      rw [show (homOfLE (le_refl U)).op = 𝟙 (op U) from Subsingleton.elim _ _]
      exact CategoryTheory.Functor.map_id _ _
    rw [he, hid]
    rfl

end AlgebraicGeometry.Scheme.Modules.PushSES

theorem
  _root_.AlgebraicGeometry.Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app
    {X T : Scheme.{u}} (π : X ⟶ T) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : ∀ (U : T.Opens), ∀ y ∈ U, ∃ V : T.Opens, y ∈ V ∧ V ≤ U ∧
      Function.Surjective (S.g.app (π ⁻¹ᵁ V))) :
    (S.map (Scheme.Modules.pushforward π)).ShortExact :=
  AlgebraicGeometry.Scheme.Modules.PushSES.shortExact π S hS hsurj
end Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end shortExact_map_pushforward_of_forall_exists_surjective_app
