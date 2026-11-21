/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Descent.FiniteQuotients

/-! # Finite quotients glued from finite local quotients -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open SchemeTheory.Descent.QuotientGluing.AlgebraicGeometry.Scheme.QuotGlue

namespace AlgebraicGeometry.Scheme

universe u

/-- The glued fppf quotient is finite when each invariant chart has a finite quotient. -/
theorem exists_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  let qdata (x : X) : ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      QuasiCompact p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p := by
    obtain ⟨Y, p, h, hf, hflat, hl, hs, hpb⟩ := loc x
    let : IsFinite p := hf
    exact ⟨Y, p, h, inferInstance, hflat, hl, hs, hpb⟩
  have hfinite (x : X) : IsFinite (ploc s t W hinv qdata x) := by
    obtain ⟨Y, p, hw₀, hfin, hflat, hlfp, hsurj, hpb₀⟩ := loc x
    let : IsFinite p := hfin
    let : Flat p := hflat
    let : LocallyOfFinitePresentation p := hlfp
    let : Surjective p := hsurj
    let q := ploc s t W hinv qdata x
    have hq := ploc_spec s t W hinv qdata x
    let : QuasiCompact q := hq.2.1
    let : Flat q := hq.2.2.1
    let : LocallyOfFinitePresentation q := hq.2.2.2.1
    let : Surjective q := hq.2.2.2.2.1
    let k₀ : IsKernelPair p (s ∣_ W x) (tW s t W hinv x) := hpb₀
    let k₁ : IsKernelPair q (s ∣_ W x) (tW s t W hinv x) := hq.2.2.2.2.2
    let c₀ : IsColimit (Cofork.ofπ p hw₀) := k₀.toCoequalizer (regularEpiOfEffectiveEpi p)
    let c₁ : IsColimit (Cofork.ofπ q hq.1) := k₁.toCoequalizer (regularEpiOfEffectiveEpi q)
    let e := c₀.coconePointUniqueUpToIso c₁
    have he : p ≫ e.hom = q :=
      IsColimit.comp_coconePointUniqueUpToIso_hom c₀ c₁ WalkingParallelPair.one
    change IsFinite q
    rw [← he]
    infer_instance
  have hAffine : HasAffineProperty (@IsFinite : MorphismProperty Scheme.{u})
      (affineAnd RingHom.Finite) :=
    (HasAffineProperty.affineAnd_iff (@IsFinite : MorphismProperty Scheme.{u})
      RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan).mpr (fun {_ _} f => isFinite_iff f)
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp hAffine).1
  let p := pglued hxW qdata
  have hfin : IsFinite p := property_pglued hxW qdata (@IsFinite.{u}) hfinite
  let : Flat p := flat_pglued hxW qdata
  let : LocallyOfFinitePresentation p := lfp_pglued hxW qdata
  let : Surjective p := surjective_pglued hxW qdata
  have hk : IsKernelPair p s t := isPullback_pglued hxW qdata
  exact ⟨_, p, s_pglued hxW qdata, hfin, inferInstance, inferInstance, inferInstance,
    hk, ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi p)⟩⟩

end AlgebraicGeometry.Scheme
