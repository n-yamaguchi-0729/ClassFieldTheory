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
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_restrictAlong_congrEquiv_and_existsUnique_iff.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le.lean
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_smul_restrictAlong.lean

Source-file correspondence is unconfirmed for:
Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
Place_restrictAlong_restrictAlong
Place_restrict_ofAlgAut_smul
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Divisors.Maps.Maps

/-!
# Place restrict Along alg Equiv eq of Alg Aut symm smul
-/

section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul

open AlgebraicCurve
open scoped Pointwise

theorem _root_.AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  change σ x ∈ v.toValuationSubring ↔ _
  rfl

end AlgebraicCurves.Places.Proofs.Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
end ProofImplementation

end

section

/-!
# Place restrict Along congr Equiv and exists Unique iff
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_congrEquiv_and_existsUnique_iff

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.restrictAlong_congrEquiv_and_existsUnique_iff
    {K E F F' : Type*} [Field K] [Field E] [Field F] [Field F'] [Algebra K E] [Algebra K F]
      [Algebra K F']
    (φ : E →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (φ' : E →ₐ[K] F') (hφ' : φ'.toRingHom.IsIntegral)
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (hcomm : ∀ x : E, e (φ x) = φ' x) :
    (∀ w : Place K F, (Place.congrEquiv e he w).restrictAlong φ' hφ' = w.restrictAlong φ hφ) ∧
    (∀ s : Place K E, ∀ w' : Place K F', w'.restrictAlong φ' hφ' = s ↔
        ((Place.congrEquiv e he).symm w').restrictAlong φ hφ = s) ∧
    (∀ s : Place K E, (∃! w : Place K F, w.restrictAlong φ hφ = s) ↔
        (∃! w' : Place K F', w'.restrictAlong φ' hφ' = s)) := by
  classical
  have h1 : ∀ w : Place K F, (Place.congrEquiv e he w).restrictAlong φ' hφ' = w.restrictAlong φ hφ
    := by
    intro w
    apply Place.ext
    ext x
    change (e.symm : F' →+* F) (φ'.toRingHom x) ∈ w.toValuationSubring ↔ φ.toRingHom x ∈
      w.toValuationSubring
    rw [show φ'.toRingHom x = φ' x from rfl, show φ.toRingHom x = φ x from rfl, ← hcomm]
    change e.symm (e (φ x)) ∈ w.toValuationSubring ↔ φ x ∈ w.toValuationSubring
    rw [e.symm_apply_apply]
  have h2 : ∀ s : Place K E, ∀ w' : Place K F', w'.restrictAlong φ' hφ' = s ↔
      ((Place.congrEquiv e he).symm w').restrictAlong φ hφ = s := by
    intro s w'
    rw [← h1 ((Place.congrEquiv e he).symm w'), Equiv.apply_symm_apply]
  refine ⟨h1, h2, fun s => ?_⟩
  constructor
  · rintro ⟨w, hw, huniq⟩
    refine ⟨Place.congrEquiv e he w, by
      change Place.restrictAlong φ' hφ' (Place.congrEquiv e he w) = s; rw [h1]; exact hw,
      fun w' hw' => ?_⟩
    have := huniq ((Place.congrEquiv e he).symm w') ((h2 s w').mp hw')
    rw [← this, Equiv.apply_symm_apply]
  · rintro ⟨w', hw', huniq⟩
    refine ⟨(Place.congrEquiv e he).symm w', (h2 s w').mp hw', fun w hw => ?_⟩
    have := huniq (Place.congrEquiv e he w)
      (by change Place.restrictAlong φ' hφ' (Place.congrEquiv e he w) = s; rw [h1]; exact hw)
    rw [← this, Equiv.symm_apply_apply]

end AlgebraicCurves.Places.Proofs.Place_restrictAlong_congrEquiv_and_existsUnique_iff
end ProofImplementation

end

section

/-!
# Place restrict Along inclusion of le of le
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_inclusion_of_le_of_le

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace ITransportSeam
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

theorem restrictAlong_incl_incl {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h₁ : S ≤ T) (h₂ : T ≤ S)
    (hι₁ : (IntermediateField.inclusion h₁).toRingHom.IsIntegral) (hι₂ :
      (IntermediateField.inclusion h₂).toRingHom.IsIntegral)
    (W : Place K ↥S) :
    (W.restrictAlong (IntermediateField.inclusion h₂) hι₂).restrictAlong
      (IntermediateField.inclusion h₁) hι₁ = W := by
  apply Place.ext
  ext x
  exact (show IntermediateField.inclusion h₂ (IntermediateField.inclusion h₁ x) ∈
    W.toValuationSubring ↔ x ∈ W.toValuationSubring by
    rw [IntermediateField.inclusion_inclusion, IntermediateField.inclusion_self, AlgHom.id_apply])

theorem ramificationIndexAlong_incl_eq_one {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h₁ : S ≤ T) (h₂ : T ≤ S)
    (hι₁ : (IntermediateField.inclusion h₁).toRingHom.IsIntegral) (hι₂ :
      (IntermediateField.inclusion h₂).toRingHom.IsIntegral)
    (W' : Place K ↥T) : W'.ramificationIndexAlong (IntermediateField.inclusion h₁) = 1 := by
  classical
  set W := W'.restrictAlong (IntermediateField.inclusion h₁) hι₁ with hW
  have hWW' : W.restrictAlong (IntermediateField.inclusion h₂) hι₂ = W' := restrictAlong_incl_incl
    h₂ h₁ hι₂ hι₁ W'
  have e1 : ∀ f : ↥S, W'.ord (IntermediateField.inclusion h₁ f) =
      Place.ramificationIndexAlong (IntermediateField.inclusion h₁) W' * W.ord f :=
    fun f => Place.ord_restrictAlong _ hι₁ W' f
  have e2 : ∀ f' : ↥T, W.ord (IntermediateField.inclusion h₂ f') =
      Place.ramificationIndexAlong (K := K) (F := T) (F' := S)
        (IntermediateField.inclusion h₂) W * W'.ord f' := by
    intro f'
    have := Place.ord_restrictAlong _ hι₂ W f'
    rwa [hWW'] at this
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  have hπ1 : W.ord (π : ↥S) = 1 := W.ord_coe_irreducible hπ
  have hprod : (Place.ramificationIndexAlong (K := K) (F := T) (F' := S)
      (IntermediateField.inclusion h₂) W : ℤ) *
      Place.ramificationIndexAlong (K := K) (F := S) (F' := T)
        (IntermediateField.inclusion h₁) W' = 1 := by
    have hh := e2 (IntermediateField.inclusion h₁ (π : ↥S))
    rw [IntermediateField.inclusion_inclusion, IntermediateField.inclusion_self, AlgHom.id_apply,
      hπ1, e1, hπ1, mul_one] at hh
    exact hh.symm
  have hone : (Place.ramificationIndexAlong (K := K) (F := S) (F' := T)
      (IntermediateField.inclusion h₁) W' : ℤ) = 1 := by
    have hnn1 : (0 : ℤ) ≤ Place.ramificationIndexAlong (K := K) (F := S) (F' := T)
      (IntermediateField.inclusion h₁) W' := Int.natCast_nonneg _
    rw [mul_comm] at hprod
    exact Int.eq_one_of_mul_eq_one_right hnn1 hprod
  exact_mod_cast hone

end AlgebraicCurve.Place.ITransportSeam

open AlgebraicCurve.Place.ITransportSeam in
theorem _root_.AlgebraicCurve.Place.restrictAlong_inclusion_of_le_of_le
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (hST : S ≤ T) (hTS : T ≤ S)
    (h : (IntermediateField.inclusion hST).toRingHom.IsIntegral)
    (h' : (IntermediateField.inclusion hTS).toRingHom.IsIntegral) :
    (∀ w : Place K T, (w.restrictAlong (IntermediateField.inclusion hST) h).restrictAlong
      (IntermediateField.inclusion hTS) h' = w) ∧
    (∀ v : Place K S, (v.restrictAlong (IntermediateField.inclusion hTS) h').restrictAlong
      (IntermediateField.inclusion hST) h = v) ∧
    (∀ w : Place K T, w.ramificationIndexAlong
      (IntermediateField.inclusion hST : S →ₐ[K] T) = 1) ∧
    (∀ (w : Place K T) (f : S),
      (w.restrictAlong (IntermediateField.inclusion hST : S →ₐ[K] T) h).ord f =
        w.ord (IntermediateField.inclusion hST f)) := by
  refine ⟨fun w => restrictAlong_incl_incl hTS hST h' h w, fun v => restrictAlong_incl_incl hST hTS
    h h' v,
    fun w => ramificationIndexAlong_incl_eq_one hST hTS h h' w, fun w f => ?_⟩
  rw [Place.ord_restrictAlong _ h w f, ramificationIndexAlong_incl_eq_one hST hTS h h' w,
    Nat.cast_one, one_mul]
end AlgebraicCurves.Places.Proofs.Place_restrictAlong_inclusion_of_le_of_le
end ProofImplementation

end

section

/-!
# Place restrict Along restrict Along
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_restrictAlong

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.restrictAlong_restrictAlong {K F F' F'' : Type*} [Field K]
  [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
  (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp
  φ).toRingHom.IsIntegral) (W : Place K F'') : (W.restrictAlong χ hχ).restrictAlong φ hφ =
  W.restrictAlong (χ.comp φ) hχφ :=
  Place.ext (SetLike.ext fun _ => Iff.rfl)
end AlgebraicCurves.Places.Proofs.Place_restrictAlong_restrictAlong
end ProofImplementation

end

section

/-!
# Place restrict of Alg Aut smul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrict_ofAlgAut_smul

noncomputable section
open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place
  _root_.AlgebraicCurves.Places.Proofs.Place_restrict_ofAlgAut_smul.AlgebraicCurve.Place in
theorem _root_.AlgebraicCurve.Place.restrict_ofAlgAut_smul {K F' M : Type*} [Field K] [Field F']
  [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [Algebra.IsIntegral F' M] (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F' := by
  refine Place.ext ?_
  ext x
  rw [restrict_toValuationSubring, restrict_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  have : ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) = algebraMap F' M x := by
    rw [RingEquiv.symm_apply_eq]
    exact (σ.commutes x).symm
  rw [this]

end
end AlgebraicCurves.Places.Proofs.Place_restrict_ofAlgAut_smul
end ProofImplementation

end

section

/-!
# Place smul restrict Along
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_smul_restrictAlong

noncomputable section

open AlgebraicCurve

namespace FibreSolG

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f :
  F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem mem_smul_iff (σ : F' ≃ₐ[K] F') (w : Place K F') (x : F') :
    x ∈ (σ • w).toValuationSubring ↔ σ.symm x ∈ w.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w :
  Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

variable (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
  (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x))
include h

theorem sq_symm (x : F) : σ.symm (α x) = β (τ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← h, AlgEquiv.apply_symm_apply]

theorem smul_restrictAlong (W : Place K F') :
    (σ • W).restrictAlong α hα = τ • (W.restrictAlong β hβ) := by
  ext f
  rw [mem_restrictAlong_iff, mem_smul_iff, sq_symm α β σ τ h,
    show f ∈ (τ • W.restrictAlong β hβ).toValuationSubring ↔ τ.symm f ∈ (W.restrictAlong β
      hβ).toValuationSubring from by
      rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]; rfl,
    mem_restrictAlong_iff]

theorem ramificationIndexAlong_smul (W : Place K F') :
    (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β := by
  change sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (σ • W).ord (α f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (β f) = n}
  congr 1
  ext n
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨τ.symm f, by simpa using hf, ?_⟩
    rw [← hn, ← sq_symm α β σ τ h f, ← Place.ord_smul σ W (σ.symm (α f)), AlgEquiv.apply_symm_apply]
  · rintro ⟨g, hg, hn⟩
    refine ⟨τ g, by simpa using hg, ?_⟩
    rw [← hn, h g, Place.ord_smul]

theorem inertiaDegAlong_smul (W : Place K F') (hdeg : (W.restrictAlong β hβ).deg = 1) :
    (σ • W).inertiaDegAlong α hα = W.inertiaDegAlong β hβ := by
  have h1 := deg_restrictAlong_mul_inertiaDegAlong (K := K) α hα (σ • W)
  have h2 := deg_restrictAlong_mul_inertiaDegAlong (K := K) β hβ W
  rw [smul_restrictAlong α β hα hβ σ τ h, Place.deg_smul, hdeg, one_mul, Place.deg_smul] at h1
  rw [hdeg, one_mul] at h2
  rw [h1, h2]

end Generic

end FibreSolG

end

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Place.smul_restrictAlong {K F F' : Type*} [Field K] [Field F] [Field
  F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ :
  β.toRingHom.IsIntegral) (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place
  K F') : (σ • W).restrictAlong α hα = τ • W.restrictAlong β hβ :=
  FibreSolG.smul_restrictAlong α β hα hβ σ τ h W
end AlgebraicCurves.Places.Proofs.Place_smul_restrictAlong
end ProofImplementation

end
