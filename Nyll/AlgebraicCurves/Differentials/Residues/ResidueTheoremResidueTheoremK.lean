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

import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Differentials.Residues.Construction

/-!
Compare the residue theorem with its base-field formulation. Over an algebraically closed
base field, uniqueness of normalized local residues also gives the reverse implication.
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_residueTheoremK


open AlgebraicCurve

theorem _root_.AlgebraicCurve.residueTheorem_of_residueTheoremK
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (h : AlgebraicCurve.ResidueTheoremK K F) :
    ∀ [AlgebraicCurve.HasPrincipalDivisors K F], AlgebraicCurve.ResidueTheorem K F := by
  intro _hPD ω hω f
  have key := h (fun v => HasCanonicalLocalResidueKStar.dataKStar v) hω f
  rw [weilOfKaehlerK_apply] at key
  rw [weilOfKaehler_apply]
  exact key
end AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_residueTheoremK
end ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheoremK_of_isAlgClosed

noncomputable section

open _root_.AlgebraicCurve

namespace AlgebraicCurve

private theorem subsingleton_canonicalLocalResidueDataK_of_surj
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField)) :
    Subsingleton v.CanonicalLocalResidueDataK := by
  constructor
  intro R₁ R₂
  have hres : R₁.res = R₂.res := by
    ext f
    obtain ⟨n, hn⟩ := v.exists_mem_poleSubmodule f
    exact v.canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj
      hsurj R₁ R₂ n hn
  obtain ⟨⟨r₁, h₁a, h₁b⟩, h₁c⟩ := R₁
  obtain ⟨⟨r₂, h₂a, h₂b⟩, h₂c⟩ := R₂
  congr 2

private theorem subsingleton_canonicalLocalResidueDataK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (v : Place K F) [v.FiniteResidue] :
    Subsingleton v.CanonicalLocalResidueDataK := by
  let _ : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
  let _ : Algebra.IsIntegral K v.ResidueField :=
    Algebra.IsIntegral.of_finite K v.ResidueField
  exact subsingleton_canonicalLocalResidueDataK_of_surj v
    (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := K) (K := v.ResidueField)).surjective

theorem residueTheoremK_of_residueTheorem_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [∀ v : Place K F, v.FiniteResidue]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hRT : ∀ [HasPrincipalDivisors K F], ResidueTheorem K F) : ResidueTheoremK K F := by
  intro Rfam _ ω hω f
  rw [weilOfKaehlerK_apply]
  calc
    ∑ᶠ v : Place K F,
        kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v =
      ∑ᶠ v : Place K F,
        kaehlerResidueTerm ω (diagonalHom K F f) v := by
      refine finsum_congr fun v => ?_
      have hsub : Subsingleton v.CanonicalLocalResidueDataK :=
        subsingleton_canonicalLocalResidueDataK_of_isAlgClosed v
      have hR : Rfam v = HasCanonicalLocalResidueKStar.dataKStar v := hsub.elim _ _
      rw [kaehlerResidueTermKFam_apply, hR]
      rfl
    _ = 0 := by
      have hzero := hRT hω f
      rw [weilOfKaehler_apply] at hzero
      exact hzero

end AlgebraicCurve

end

end AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheoremK_of_isAlgClosed
