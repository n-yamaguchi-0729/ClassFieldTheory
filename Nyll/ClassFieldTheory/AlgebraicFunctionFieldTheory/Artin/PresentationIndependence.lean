/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationSymbol
public import Nyll.ClassFieldTheory.Algebra.GaloisAbelianization

/-!
# Independence from fixed-field presentation isomorphisms

The norm-quotient transport depends on the base inclusion, while changing
the upper isomorphism changes Galois transport by an inner automorphism.
Thus the resulting reciprocity isomorphism is unchanged.
-/

@[expose] public section

universe u v w x

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

private theorem abelianizationCongr_trans_autCongr_eq
    {G F E D : Type*} [Group G] [Field F] [Field E] [Field D]
    [Algebra F E] [Algebra F D]
    (r : G ≃* Gal(E/F)) (a b : E ≃ₐ[F] D) (z : Abelianization G) :
    (r.trans (AlgEquiv.autCongr a)).abelianizationCongr z =
      (r.trans (AlgEquiv.autCongr b)).abelianizationCongr z := by
  refine QuotientGroup.induction_on z ?_
  intro g
  exact congrArg
    (fun f : Abelianization (Gal(E/F)) ≃* Abelianization (Gal(D/F)) =>
      f (Abelianization.of (r g)))
    (ClassFieldTheory.autCongr_abelianizationCongr_eq a b)

variable (k : Type u) (K : Type v) (L : Type w) (Ω : Type x)
    [Field k] [Finite k] [Field K] [Field L] [Field Ω]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Changing the isomorphisms to the same fixed fields does not change reciprocity. -/
theorem normQuotientEquivOfFixedFieldPresentation_eq
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (eF eF' : K ≃ₐ[K] abstractFixedField K Ω H.field)
    (eE eE' : L ≃ₐ[K] abstractFixedField K Ω T.field) :
    normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eE =
      normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF' eE' := by
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro c
  rw [normQuotientEquivOfFixedFieldPresentation_mk k K L Ω H T eF eE c,
    normQuotientEquivOfFixedFieldPresentation_mk k K L Ω H T eF' eE' c]
  simp only [AlgEquiv.autCongr_symm]
  exact abelianizationCongr_trans_autCongr_eq _ eE.symm eE'.symm _

end FunctionField
