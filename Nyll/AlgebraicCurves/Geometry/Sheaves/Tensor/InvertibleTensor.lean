/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.SchemeTheory.Modules.PresheafInternalHom
public import Nyll.SchemeTheory.Modules.Tensor.SheafificationMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.PresheafPullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.SchemeTheory.Modules.Invertible.Invertible

/-!
# Tensor products of invertible module sheaves

Restrict local trivializations to their common open subset and tensor them to prove
that the tensor product of two invertible modules is invertible.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_tensor

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
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

/-- Pull a trivialization of `L` back from `U` to the smaller open `V`. -/
noncomputable def trivializationOfLE {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor {X :
    AlgebraicGeometry.Scheme.{u}}
    {L M : X.Modules} (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (L ⊗ M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  obtain ⟨U', hxU', ⟨eU'⟩⟩ := hM.1 x
  refine ⟨U ⊓ U', ⟨hxU, hxU'⟩, ⟨?_⟩⟩
  exact pullbackTensorObjIso (U ⊓ U').ι L M ≪≫
    (trivializationOfLE inf_le_left L eU ⊗ᵢ trivializationOfLE inf_le_right M eU') ≪≫
    λ_ (𝟙_ _)

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-- Every nonnegative tensor power of an invertible module is invertible. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorPow
    {X : _root_.AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible L) (n : ℕ) :
    _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible (L.tensorPow n) := by
  induction n with
  | zero => exact _root_.AlgebraicGeometry.Scheme.Modules.isInvertible_unit X
  | succ n ih => exact ih.tensor hL

end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_tensor
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
