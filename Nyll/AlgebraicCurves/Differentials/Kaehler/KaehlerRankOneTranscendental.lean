/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Differentials, residues, and divisor correspondences

Singleton bases for polynomial and rational-function differentials and their separable field
extensions.
-/

@[expose] public section

namespace KaehlerDifferential

open scoped Polynomial
open IntermediateField TensorProduct

variable (K : Type*) [Field K]

/-- The one-element basis of polynomial differentials given by the variable differential. -/
noncomputable def polynomialBasis : Module.Basis (Fin 1) K[X] Ω[K[X]⁄K] :=
  (Module.Basis.singleton (Fin 1) K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

theorem polynomialBasis_zero : polynomialBasis K 0 = D K K[X] Polynomial.X := by
  simp only [polynomialBasis, Module.Basis.map_apply, Module.Basis.singleton_apply,
    KaehlerDifferential.polynomialEquiv_symm, one_smul]

/-- The one-element basis of rational-function differentials obtained by localization. -/
noncomputable def ratFuncBasis : Module.Basis (Fin 1) (RatFunc K) Ω[(RatFunc K)⁄K] :=
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  ((polynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem ratFuncBasis_zero : ratFuncBasis K 0 = D K (RatFunc K) RatFunc.X := by
  have : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  simp only [ratFuncBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    polynomialBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
    RatFunc.algebraMap_X]

variable {F : Type*} [Field F] [Algebra K F]

/-- Extend the differential basis along the separable function-field extension. -/
noncomputable def ratFuncTowerBasis [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Module.Basis (Fin 1) F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  ((ratFuncBasis K).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) F)

theorem ratFuncTowerBasis_zero [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] :
    ratFuncTowerBasis K (F := F) 0 = D K F (algebraMap (RatFunc K) F RatFunc.X) := by
  have : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  simp only [ratFuncTowerBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    ratFuncBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

/-- Kähler differentials of the rational function field are free of rank one. -/
theorem rankOne_ratFunc :
    Module.Free (RatFunc K) Ω[(RatFunc K)⁄K] ∧
      Module.finrank (RatFunc K) Ω[(RatFunc K)⁄K] = 1 :=
  ⟨Module.Free.of_basis (ratFuncBasis K),
    (Module.finrank_eq_card_basis (ratFuncBasis K)).trans (Fintype.card_fin 1)⟩

/-- A separating transcendental coordinate gives its differential as a basis vector. -/
theorem exists_basis_eq_D_of_transcendental (F : Type*) [Field F] [Algebra K F] [CharZero K]
    {t : F} (ht : Transcendental K t) (hfin : FiniteDimensional K⟮t⟯ F) :
    ∃ b : Module.Basis (Fin 1) F (Ω[F⁄K]), b 0 = D K F t := by
  have := hfin
  have : CharZero K⟮t⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮t⟯).injective
  have : Algebra.IsSeparable K⟮t⟯ F := Algebra.IsSeparable.of_integral K⟮t⟯ F
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  let : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    change algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  refine ⟨ratFuncTowerBasis K, ?_⟩
  rw [ratFuncTowerBasis_zero]
  change D K F (algebraMap K⟮t⟯ F (e RatFunc.X)) = D K F t
  congr 1
  exact RatFunc.algEquivOfTranscendental_X t ht

end KaehlerDifferential

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.KaehlerRankOne_of_transcendental

noncomputable section

open IntermediateField Polynomial TensorProduct Module

namespace S12Kaehler

variable (K : Type*) [Field K]

variable {F : Type*} [Field F] [Algebra K F]

theorem kaehlerRankOne_of_ratFuncTower [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=
  ⟨Module.Free.of_basis (KaehlerDifferential.ratFuncTowerBasis K),
    (Module.finrank_eq_card_basis (KaehlerDifferential.ratFuncTowerBasis K)).trans
      (Fintype.card_fin 1)⟩

variable {K}

theorem kaehlerRankOne_of_transcendental {x : F} (htr : Transcendental K x)
    (hsep : Algebra.IsSeparable K⟮x⟯ F) : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by
  have := hsep
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  let : Algebra (RatFunc K) F :=
    ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    change algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact kaehlerRankOne_of_ratFuncTower K

end S12Kaehler

end

theorem _root_.AlgebraicCurve.kaehlerRankOne_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by
  exact S12Kaehler.kaehlerRankOne_of_transcendental htr hsep
end AlgebraicCurves.Differentials.Proofs.KaehlerRankOne_of_transcendental
end ProofImplementation
