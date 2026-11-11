/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.PushoutKernel

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Tactic.Algebraize
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.RelEffCartierDiv
public import Nyll.SchemeTheory.RingTheory.IdealMapComapEqSelfMapIncludeLeftEqMapIncludeRight
public import Nyll.SchemeTheory.Sheaves.IdealSheafComap
public import Mathlib.Util.WithWeakNamespace

/-!
# Differentials, residues, and divisor correspondences

Faithfully flat affine pullback descends a relative effective Cartier divisor, using the tensor-
product kernel formula.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Algebra
open _root_.Algebra
namespace IsPushout
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
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_top I f


theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le I f U V hVU

theorem ideal_comap_of_isAffineHom (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = (I.ideal U).map (f.app U).hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isAffineHom I f U

end AlgebraicGeometry.Scheme.IdealSheafData

namespace RingHom
open _root_.RingHom
namespace Flat
open _root_.RingHom.Flat
end RingHom.Flat
open scoped _root_.RingHom _root_.RingHom.Flat in
lemma RingHom.Flat.codescendsAlong_faithfullyFlat' :
    RingHom.CodescendsAlong (fun f => RingHom.Flat f) (fun f => RingHom.FaithfullyFlat f) := by
  refine RingHom.CodescendsAlong.mk _ RingHom.Flat.respectsIso ?_
  intro R S T _ _ _ _ _ h H
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  rw [RingHom.flat_algebraMap_iff] at H ⊢
  exact Module.Flat.of_flat_tensorProduct R T S

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Flat
open _root_.AlgebraicGeometry.Flat
end AlgebraicGeometry.Flat
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Flat in
scoped instance AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat_inf_quasicompact' :
    MorphismProperty.DescendsAlong @AlgebraicGeometry.Flat
      (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.QuasiCompact) :=
  AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat
    RingHom.Flat.codescendsAlong_faithfullyFlat'

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace AffineDescent
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} [IsAffine 𝒞] [IsAffine S] {f : 𝒞 ⟶ S} {r : ℕ}
  {X Y R : Scheme.{u}} [IsAffine X] [IsAffine Y] {gX : X ⟶ S} {gY : Y ⟶ S} {gR : R ⟶ S}
  (p : X ⟶ Y) (hp : p ≫ gY = gX)
  (s t : R ⟶ X) (hs : s ≫ gX = gR) (ht : t ≫ gX = gR) (hR : IsPullback s t p p)

include hR in
omit [IsAffine 𝒞] [IsAffine S] [IsAffine X] [IsAffine Y] in
lemma isPullback_mapOnProdOver_kernelPair :
    IsPullback (mapOnProdOver f s hs) (mapOnProdOver f t ht)
      (mapOnProdOver f p hp) (mapOnProdOver f p hp) := by
  have outer := (isPullback_mapOnProdOver f s hs).paste_vert hR
  rw [← mapOnProdOver_snd f t ht, ← mapOnProdOver_snd f p hp] at outer
  refine IsPullback.of_bot outer ?_ (isPullback_mapOnProdOver f p hp)
  apply pullback.hom_ext
  · simp only [Category.assoc, mapOnProdOver_fst]
  · simp only [Category.assoc, mapOnProdOver_snd, mapOnProdOver_snd_assoc, hR.w]

variable [IsFinite p] [Flat p] [Surjective p]

include hp in
omit [IsFinite p] in
lemma faithfullyFlat_appTop_mapOnProdOver :
    letI := (mapOnProdOver f p hp).appTop.hom.toAlgebra
    Module.FaithfullyFlat Γ(pullback f gY, ⊤) Γ(pullback f gX, ⊤) := by
  have : IsAffine (pullback f gY) := isAffine_of_isAffineHom (pullback.snd f gY)
  have : IsAffine (pullback f gX) := isAffine_of_isAffineHom (pullback.snd f gX)
  set π := mapOnProdOver f p hp
  have : Flat π := MorphismProperty.of_isPullback (isPullback_mapOnProdOver f p hp).flip
    inferInstance
  have : Surjective π :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f p hp).flip inferInstance
  let := π.appTop.hom.toAlgebra
  have : Module.Flat Γ(pullback f gY, ⊤) Γ(pullback f gX, ⊤) := Scheme.Hom.flat_appTop π
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  have hsurj : Surjective (Spec.map π.appTop) := by
    have : Spec.map π.appTop = (pullback f gX).isoSpec.inv ≫ π ≫ (pullback f gY).isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  exact hsurj.surj

end AlgebraicGeometry.RelEffCartierDiv.AffineDescent

open _root_.AlgebraicGeometry in
with_weak_namespace _root_.AlgebraicCurves.RelativeDivisors.Proofs
with_weak_namespace RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
with_weak_namespace AlgebraicGeometry
open RelEffCartierDiv.AffineDescent in
theorem
  _root_.AlgebraicGeometry.RelEffCartierDiv.existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
    {𝒞 S : Scheme.{u}} [IsAffine 𝒞] [IsAffine S] {f : 𝒞 ⟶ S} {r : ℕ}
    {X Y R : Scheme.{u}} [IsAffine X] [IsAffine Y] {gX : X ⟶ S} {gY : Y ⟶ S} {gR : R ⟶ S}
    (p : X ⟶ Y) (hp : p ≫ gY = gX)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (s t : R ⟶ X) (hs : s ≫ gX = gR) (ht : t ≫ gX = gR) (hR : IsPullback s t p p)
    (D : RelEffCartierDiv f r gX) (hD : D.pullbackAlong s hs = D.pullbackAlong t ht) :
    ∃! DY : RelEffCartierDiv f r gY, DY.pullbackAlong p hp = D := by
  classical
  have : IsAffine (pullback f gY) := isAffine_of_isAffineHom (pullback.snd f gY)
  have : IsAffine (pullback f gX) := isAffine_of_isAffineHom (pullback.snd f gX)
  have : IsAffineHom s := MorphismProperty.of_isPullback hR.flip inferInstance
  have : IsAffine R := isAffine_of_isAffineHom s
  have : IsAffine (pullback f gR) := isAffine_of_isAffineHom (pullback.snd f gR)
  set π := mapOnProdOver f p hp with hπ
  have : Flat π := MorphismProperty.of_isPullback (isPullback_mapOnProdOver f p hp).flip
    inferInstance
  have : Surjective π :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f p hp).flip inferInstance
  have huniq : ∀ DY DY' : RelEffCartierDiv f r gY,
      DY.pullbackAlong p hp = D → DY'.pullbackAlong p hp = D → DY = DY' := by
    intro DY DY' h h'
    refine RelEffCartierDiv.ext (Scheme.IdealSheafData.comap_injective_of_flat_of_surjective π ?_)
    exact (congrArg RelEffCartierDiv.I h).trans (congrArg RelEffCartierDiv.I h').symm
  suffices hex : ∃ DY : RelEffCartierDiv f r gY, DY.pullbackAlong p hp = D by
    obtain ⟨DY, hDY⟩ := hex
    exact ⟨DY, hDY, fun DY' hDY' => huniq DY' DY hDY' hDY⟩
  let alg := π.appTop.hom.toAlgebra
  have : Module.FaithfullyFlat Γ(pullback f gY, ⊤) Γ(pullback f gX, ⊤) :=
    faithfullyFlat_appTop_mapOnProdOver p hp
  have h1 := isPushout_appTop_of_isPullback
    (isPullback_mapOnProdOver_kernelPair (f := f) p hp s t hs ht hR)
  have h2 : IsPushout π.appTop π.appTop
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(pullback f gX, ⊤) →+* Γ(pullback f gX, ⊤) ⊗[Γ(pullback f gY, ⊤)] Γ(pullback f gX, ⊤)))
      (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        Γ(pullback f gX, ⊤) →ₐ[Γ(pullback f gY, ⊤)]
          Γ(pullback f gX, ⊤) ⊗[Γ(pullback f gY, ⊤)] Γ(pullback f gX, ⊤)) :
        Γ(pullback f gX, ⊤) →+* Γ(pullback f gX, ⊤) ⊗[Γ(pullback f gY, ⊤)] Γ(pullback f gX,
          ⊤))) := by
    exact CommRingCat.isPushout_tensorProduct Γ(pullback f gY, ⊤) Γ(pullback f gX,
      ⊤) Γ(pullback f gX, ⊤)
  let e := h1.isoIsPushout _ _ h2
  have heL : e.hom.hom.comp (mapOnProdOver f s hs).appTop.hom =
    Algebra.TensorProduct.includeLeftRingHom := by
    rw [← CommRingCat.hom_comp, IsPushout.inl_isoIsPushout_hom, CommRingCat.hom_ofHom]
  have heR : e.hom.hom.comp (mapOnProdOver f t ht).appTop.hom =
      ((Algebra.TensorProduct.includeRight :
        Γ(pullback f gX, ⊤) →ₐ[Γ(pullback f gY, ⊤)]
          Γ(pullback f gX, ⊤) ⊗[Γ(pullback f gY, ⊤)] Γ(pullback f gX, ⊤)) : _ →+* _) := by
    rw [← CommRingCat.hom_comp, IsPushout.inr_isoIsPushout_hom, CommRingCat.hom_ofHom]
  set IB : Ideal Γ(pullback f gX, ⊤) := D.I.ideal ⟨⊤, isAffineOpen_top _⟩ with hIB
  have hinv : D.I.comap (mapOnProdOver f s hs) = D.I.comap (mapOnProdOver f t ht) :=
    congrArg RelEffCartierDiv.I hD
  have hinv' : IB.map (mapOnProdOver f s hs).appTop.hom = IB.map
    (mapOnProdOver f t ht).appTop.hom := by
    rw [hIB, ← Scheme.IdealSheafData.ideal_comap_top, ← Scheme.IdealSheafData.ideal_comap_top, hinv]
  have hDC : IB.map (Algebra.TensorProduct.includeLeftRingHom :
        Γ(pullback f gX, ⊤) →+* Γ(pullback f gX, ⊤) ⊗[Γ(pullback f gY, ⊤)] Γ(pullback f gX, ⊤)) =
      IB.map ((Algebra.TensorProduct.includeRight :
        Γ(pullback f gX, ⊤) →ₐ[Γ(pullback f gY, ⊤)]
          Γ(pullback f gX, ⊤) ⊗[Γ(pullback f gY, ⊤)] Γ(pullback f gX, ⊤)) : _ →+* _) := by
    rw [← heL, ← heR, ← Ideal.map_map, ← Ideal.map_map, hinv']
  have hdesc := Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight IB hDC
  set IA : Ideal Γ(pullback f gY, ⊤) := IB.comap (algebraMap _ _) with hIA
  let DYI : (pullback f gY).IdealSheafData := Scheme.IdealSheafData.ofIdealTop IA
  have hDYI : DYI.ideal ⟨⊤, isAffineOpen_top _⟩ = IA :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply IA
  have key : DYI.comap π = D.I := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.IdealSheafData.ideal_comap_top, hDYI]
    exact hdesc
  have sq := isPullback_comap_snd_over DYI p hp
  set zY := DYI.subschemeι ≫ pullback.snd f gY with hzY
  set zX := (DYI.comap (mapOnProdOver f p hp)).subschemeι ≫ pullback.snd f gX with hzX
  have : IsFinite zX := by rw [hzX, key]; exact D.isFinite
  have : Flat zX := by rw [hzX, key]; exact D.flat
  have : LocallyOfFinitePresentation zX := by rw [hzX, key]; exact D.locallyOfFinitePresentation
  have hrkX : ∀ x, zX.finrank x = r := by rw [hzX, key]; exact D.finrank_eq
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) p :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let : MorphismProperty.DescendsAlong @Flat
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) :=
    AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat_inf_quasicompact'
  have : Flat zY :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip hQ inferInstance
  have : LocallyOfFinitePresentation zY :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFinitePresentation)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip hQ inferInstance
  have : LocallyOfFiniteType zY :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip hQ inferInstance
  have : UniversallyClosed zY :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip hQ inferInstance
  have : IsAffine DYI.subscheme := isAffine_of_isAffineHom DYI.subschemeι
  have : IsIntegralHom zY :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have : IsFinite zY := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType zY).2
    ⟨inferInstance, inferInstance⟩
  have hrkY : ∀ y, zY.finrank y = r := by
    intro y
    obtain ⟨x, rfl⟩ := p.surjective y
    rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ sq x]
    exact hrkX x
  exact ⟨⟨DYI, ‹_›, ‹_›, ‹_›, hrkY⟩, RelEffCartierDiv.ext key⟩
end RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
