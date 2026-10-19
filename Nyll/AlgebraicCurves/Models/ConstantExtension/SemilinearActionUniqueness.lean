/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction

/-!
# Uniqueness of the actual semilinear action

The action on germs determines the function-field automorphism. Together with
the pullback projections, this identifies the semilinear automorphism attached
to a specified automorphism of the constant field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicCurve

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

/-- A semilinear automorphism is determined by its actual function-field automorphism. -/
theorem SemilinearAut.toRingAut_injective {K F : Type*} [Field K] [Field F] [Algebra K F] :
    Function.Injective (SemilinearAut.toRingAut : SemilinearAut K F → F ≃+* F) := by
  intro g h hgh
  apply Subtype.ext
  apply Prod.ext hgh
  apply RingEquiv.ext
  intro a
  apply (algebraMap K F).injective
  exact (SemilinearAut.commutes g a).symm.trans
    ((congrArg (fun e : F ≃+* F => e (algebraMap K F a)) hgh).trans
      (SemilinearAut.commutes h a))

namespace CurveModel

variable {K F : Type} [Field K] [Field F] [Algebra K F] (M : CurveModel K F)

/-- The formulas on actual germs uniquely determine the semilinear automorphism. -/
theorem semilinearAut_eq_of_germ_action (θ : M.C ≅ M.C) (g h : SemilinearAut K F)
    (hg : ∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
      g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
        M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U) ((θ.hom.app U).hom t)))
    (hh : ∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
      h • M.ffEquiv.symm (M.C.germToFunctionField U t) =
        M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U) ((θ.hom.app U).hom t))) :
    g = h := by
  apply SemilinearAut.toRingAut_injective
  apply RingEquiv.ext
  intro z
  obtain ⟨U, hU, t, ht⟩ := M.C.presheaf.exists_germ_eq (M.ffEquiv z)
  let : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨genericPoint M.C, hU⟩⟩
  let : Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U)) :=
    ⟨⟨θ.inv (genericPoint M.C), by
      change θ.hom (θ.inv (genericPoint M.C)) ∈ U
      rw [← Scheme.Hom.comp_apply, θ.inv_hom_id]
      exact hU⟩⟩
  have hz : M.ffEquiv.symm (M.C.germToFunctionField U t) = z := by
    change M.ffEquiv.symm (M.C.presheaf.germ U (genericPoint M.C) hU t) = z
    rw [ht, RingEquiv.symm_apply_apply]
  change g • z = h • z
  exact (congrArg (g • ·) hz).symm.trans
    ((hg U t).trans ((hh U t).symm.trans (congrArg (h • ·) hz)))

/-- The two projections uniquely specify the automorphism of the actual base-changed curve. -/
theorem baseChange_iso_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {F : Type} [Field F] [Algebra Ω F] (M : CurveModel Ω F)
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    (e : M.C ≅ pullback c (AlgebraicGeometry.SmoothProperCurve.specMap k Ω))
    (he : e.hom ≫ pullback.snd c (AlgebraicGeometry.SmoothProperCurve.specMap k Ω) = M.toBase)
    (θ ψ : M.C ≅ M.C)
    (hp : θ.hom ≫ e.hom ≫ pullback.fst c (AlgebraicGeometry.SmoothProperCurve.specMap k Ω) =
      ψ.hom ≫ e.hom ≫ pullback.fst c (AlgebraicGeometry.SmoothProperCurve.specMap k Ω))
    (hb : θ.hom ≫ M.toBase = ψ.hom ≫ M.toBase) : θ = ψ := by
  apply Iso.ext
  apply (cancel_mono e.hom).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc] using hp
  · simpa only [Category.assoc, he] using hb

end CurveModel
end AlgebraicCurve
