/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_comap_injective_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.PushoutKernel

public import Mathlib.Util.WithWeakNamespace
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Affine ideals of an inverse image

The inverse image of an ideal sheaf is computed on affine opens by extension
of the original ideal along the induced homomorphism on sections.
-/

@[expose] public section

section IdealSheafData_ideal_comap_of_le

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_ideal_comap_of_le

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Algebra
open _root_.Algebra
namespace IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra

theorem ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  exact _root_.Algebra.IsPushout.ker_algebraMap_eq_map_ker R B C P hC

end Algebra.IsPushout

namespace CommRingCat
open _root_.CommRingCat
open _root_.CommRingCat

theorem ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  exact _root_.CommRingCat.ker_eq_map_ker_of_isPushout h hg

end CommRingCat

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
namespace ComapLocal
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f I.subschemeι)
  have := CommRingCat.ker_eq_map_ker_of_isPushout H
    (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩)
  rw [← ker_subschemeι_app I ⟨⊤, isAffineOpen_top X⟩, comap, Scheme.Hom.ker_apply]
  exact this


theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom := by
  suffices key : ∀ (U' : X.affineOpens) (V' : Y.affineOpens),
      U' = ⟨(U : X.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using U.2⟩ →
      V' = ⟨(V : Y.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using V.2⟩ →
      ∀ (e : (V' : Y.Opens) ≤ f ⁻¹ᵁ (U' : X.Opens)),
        (I.comap f).ideal V' = (I.ideal U').map (f.appLE U' V' e).hom from
    key U V (Subtype.ext (U : X.Opens).ι_image_top.symm)
      (Subtype.ext (V : Y.Opens).ι_image_top.symm) hVU
  rintro _ _ rfl rfl e
  have : IsAffine (U : X.Opens) := U.2
  have : IsAffine (V : Y.Opens) := V.2
  have h := ideal_comap_top (I.comap (U : X.Opens).ι) (f.resLE U V hVU)
  rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp,
    ideal_comap_of_isOpenImmersion (I.comap f) (V : Y.Opens).ι,
    ideal_comap_of_isOpenImmersion I (U : X.Opens).ι] at h
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at h
  convert h using 2 <;> try rfl
  congr 1
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, eqToHom_op]
  erw [Scheme.Hom.map_appLE_assoc, Scheme.Hom.appLE_map]

theorem ideal_comap_of_isAffineHom (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = (I.ideal U).map (f.app U).hom := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ideal_comap_of_le I f U ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ le_rfl

/-- On affine schemes, inverse image extends the ideal along the map on global sections. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_top
    [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom :=
  open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
  open Scheme_IdealSheafData_ideal_comap_of_le.AlgebraicGeometry.Scheme.IdealSheafData in
  ComapLocal.ideal_comap_top I f

/-- On the inverse image of an affine open, an affine morphism extends its defining ideal. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isAffineHom
    (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f] (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = (I.ideal U).map (f.app U).hom :=
  open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
  open Scheme_IdealSheafData_ideal_comap_of_le.AlgebraicGeometry.Scheme.IdealSheafData in
  ComapLocal.ideal_comap_of_isAffineHom I f U

end AlgebraicGeometry.Scheme.IdealSheafData.ComapLocal

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open CategoryTheory _root_.AlgebraicGeometry
    Scheme_IdealSheafData_ideal_comap_of_le.AlgebraicGeometry in
with_weak_namespace Scheme_IdealSheafData_ideal_comap_of_le
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom :=
  AlgebraicGeometry.Scheme.IdealSheafData.ComapLocal.ideal_comap_of_le I f U V hVU
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_ideal_comap_of_le
end ProofImplementation

end IdealSheafData_ideal_comap_of_le

section IdealSheafData_comap_injective_of_flat_of_surjective

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_comap_injective_of_flat_of_surjective

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective
    {X Y : Scheme.{u}} (π : Y ⟶ X) [Flat π] [Surjective π] :
    Function.Injective fun I : X.IdealSheafData => I.comap π := by
  intro I J h
  change I.comap π = J.comap π at h
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  have hU : IsAffineOpen (U : X.Opens) := U.2
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let 𝔭 : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
  obtain ⟨y, hy⟩ := π.surjective (hU.fromSpec 𝔭)
  have hyU : y ∈ π ⁻¹ᵁ (U : X.Opens) := by
    change π y ∈ (U : X.Opens)
    rw [hy, ← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self 𝔭
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (π ⁻¹ᵁ (U : X.Opens)).isOpen
  have hφ : (π.appLE U V hVU).hom.Flat := Flat.flat_appLE π hU hV hVU
  let 𝔮 : PrimeSpectrum Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩
  have h𝔮 : P = 𝔮.asIdeal.comap (π.appLE U V hVU).hom := by
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) hU V hV hVU hyV
    have h2 : hU.primeIdealOf ⟨π y, hVU hyV⟩ = 𝔭 :=
      hU.fromSpec.isOpenEmbedding.injective (by rw [IsAffineOpen.fromSpec_primeIdealOf]; exact hy)
    exact (congrArg PrimeSpectrum.asIdeal (h1.trans h2)).symm
  have hIJ : (I.ideal U).map (π.appLE U V hVU).hom = (J.ideal U).map (π.appLE U V hVU).hom := by
    rw [← Scheme.IdealSheafData.ideal_comap_of_le I π U ⟨V, hV⟩ hVU,
      ← Scheme.IdealSheafData.ideal_comap_of_le J π U ⟨V, hV⟩ hVU, h]
  let ψ := Localization.localRingHom P 𝔮.asIdeal (π.appLE U V hVU).hom h𝔮
  have hψ : ψ.Flat := RingHom.Flat.localRingHom hφ 𝔮.asIdeal P h𝔮
  let := ψ.toAlgebra
  have : Module.Flat (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal) := hψ
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal)) :=
    show IsLocalHom ψ from inferInstance
  have : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  suffices hloc : ((I.ideal U).map (algebraMap _ (Localization.AtPrime P))).map
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal)) =
      ((J.ideal U).map (algebraMap _ (Localization.AtPrime P))).map
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal)) by
    have := congrArg
      (Ideal.comap (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal))) hloc
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat,
      Ideal.comap_map_eq_self_of_faithfullyFlat] at this
  have hcomm : ψ.comp (algebraMap Γ(X, U) (Localization.AtPrime P)) =
      (algebraMap Γ(Y, V) (Localization.AtPrime 𝔮.asIdeal)).comp (π.appLE U V hVU).hom :=
    RingHom.ext fun x => Localization.localRingHom_to_map P 𝔮.asIdeal _ h𝔮 x
  rw [Ideal.map_map, Ideal.map_map, RingHom.algebraMap_toAlgebra, hcomm, ← Ideal.map_map,
    ← Ideal.map_map, hIJ]

end Scheme_IdealSheafData_comap_injective_of_flat_of_surjective
end AlgebraicCurves.Geometry.Sheaves.Proofs

end IdealSheafData_comap_injective_of_flat_of_surjective

section IdealSheafData_comap_mul

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_comap_mul

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_mul {X Y : Scheme.{u}}
    (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  let ι := Σ U : Y.affineOpens, {V : X.affineOpens // (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : ι ↦ i.2.1) ?_ ?_
  · refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hVU⟩, hxV⟩
  · rintro ⟨U, V, hVU⟩
    change ((I * J).comap f).ideal V = (I.comap f * J.comap f).ideal V
    rw [_root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le _ f U V hVU]
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    rw [_root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le I f U V hVU,
      _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le J f U V hVU, Ideal.map_mul]

end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_comap_mul

end IdealSheafData_comap_mul

section IdealSheafData_eq_of_forall_comap_openCover_eq

/-!
# Equality of ideal sheaves on an open cover

Ideal-sheaf data agree when their pullbacks to every member of an open cover agree.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem eq_of_forall_comap_openCover_eq_aux
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  refine ext_of_iSup_eq_top
    (fun p : Σ i, (𝒰.X i).affineOpens => ⟨𝒰.f p.1 ''ᵁ (p.2 : (𝒰.X p.1).Opens),
      p.2.2.image_of_isOpenImmersion _⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      (𝒰.X (𝒰.idx x)).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨𝒰.idx x, ⟨W, hW⟩⟩, ⟨y, hyW, hy⟩⟩
  · rintro ⟨i, W⟩
    have hW := congrArg (fun K : (𝒰.X i).IdealSheafData => K.ideal W) (h i)
    simp only [ideal_comap_of_isOpenImmersion] at hW
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv).2 hW

end AlgebraicGeometry.Scheme.IdealSheafData

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq_aux 𝒰 h
end Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end IdealSheafData_eq_of_forall_comap_openCover_eq

section IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range

/-!
# Scheme Ideal Sheaf Data exists iso subscheme comap of support subset range
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsOpenImmersion ψ]
    (h : (I.support : Set X) ⊆ Set.range ψ) :
    ∃ e : (I.comap ψ).subscheme ≅ I.subscheme, e.hom ≫ I.subschemeι = (I.comap ψ).subschemeι ≫ ψ :=
      by
  have hZU : ∀ z : I.subscheme, I.subschemeι z ∈ Set.range ⇑ψ := by
    intro z
    apply h
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  let _ : IsIso (pullback.snd ψ I.subschemeι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Scheme.Pullback.range_snd]
    exact hZU z
  refine ⟨I.comapIso ψ ≪≫ asIso (pullback.snd ψ I.subschemeι), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
end Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range

section IdealSheafData_comap_ofIdealTop

/-!
# Scheme Ideal Sheaf Data comap of Ideal Top
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_comap_ofIdealTop

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop
    {X Y : Scheme.{u}} (I : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f
      = Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  let ι := {p : X.affineOpens × Y.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : Y.Opens)}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : ι => i.1.1) ?_ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩
  · rintro ⟨⟨U, V⟩, hUV⟩
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le _ f V U hUV,
      Scheme.IdealSheafData.ofIdealTop_ideal,
      Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE]
    rw [← Category.assoc, f.naturality, Category.assoc, ← Functor.map_comp]
    rfl
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_comap_ofIdealTop
end ProofImplementation

end IdealSheafData_comap_ofIdealTop
