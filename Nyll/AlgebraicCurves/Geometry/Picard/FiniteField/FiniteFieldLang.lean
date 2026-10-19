/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicPointsEquivariance
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLangPowers

/-!
# Lang surjectivity on the actual geometric Picard group

For a pointed finite-field curve, construct its representing Picard scheme and
Abel--Jacobi map. The proved equivariant comparison with actual divisor classes
transports Lang surjectivity to the genuine semilinear Frobenius on its geometric
function field. A Picard representation or a Lang hypothesis is not an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve

namespace JacobianVarieties.Picard

attribute [local instance]
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

/-- Actual geometric Picard classes satisfy Lang surjectivity for every positive Frobenius power. -/
theorem exists_pic0_frobenius_lang
    {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (M : CurveModel Ω F) (eC : M.C ≅ pullback c (specMap k Ω))
    (heC : eC.hom ≫ pullback.snd c (specMap k Ω) = M.toBase) :
    ∃ (g : SemilinearAut Ω F) (θ : M.C ≅ M.C),
      θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k Ω) =
        eC.hom ≫ pullback.fst c (specMap k Ω) ∧
      θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toRingHom) ∧
      SemilinearAut.baseAut g =
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toRingEquiv ∧
      (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
        g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
          M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U)
            ((θ.hom.app U).hom t))) ∧
      ∀ n : ℕ, n ≠ 0 → Function.Surjective (fun z : Pic0 Ω F => g ^ n • z - z) := by
  obtain ⟨D, ⟨hD⟩, hs, hp, hg⟩ := exists_representsRelSubPic_of_field k c ε
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hp
  have : GeometricallyConnected D.toBase := hg
  obtain ⟨aj, -, hclass⟩ := exists_abelJacobi_of_representsRelSubPic k c ε D hD
  let L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let hc : L.IsCommutative :=
    RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
  obtain ⟨e, -, he⟩ := exists_pic0_algPoints_equivariant_of_abelJacobi
    c ε D hD aj hclass M eC heC
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω
  obtain ⟨θ, g, hproj, hbase, hconst, hfun, -, heq⟩ := he σ
  refine ⟨g, θ, hproj, hbase, hconst, hfun, ?_⟩
  let : D.P.Over (Spec (CommRingCat.of k)) := ⟨D.toBase⟩
  have hA : AbelianSchemePropertyBundle k D.toBase :=
    ⟨hs, hp, D.toBase.isConnected_preimage_singleton, ⟨L⟩⟩
  have hen (n : ℕ) (z : Pic0 Ω F) : e (g ^ n • z) = σ ^ n • e z := by
    induction n with
    | zero => simp only [pow_zero, one_smul]
    | succ n ih => rw [pow_succ', mul_smul, heq, ih, pow_succ', mul_smul]
  intro n hn z
  obtain ⟨y, hy⟩ := RelativeGroupLaw.surjective_frobenius_pow_sub k Ω D.P L hc hA n hn (e z)
  refine ⟨e.symm y, e.injective ?_⟩
  rw [map_sub, hen]
  exact (e.apply_symm_apply y).symm ▸ hy

end JacobianVarieties.Picard
