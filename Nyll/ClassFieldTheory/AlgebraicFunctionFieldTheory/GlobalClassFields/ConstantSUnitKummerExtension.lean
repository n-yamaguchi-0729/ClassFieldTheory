/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantCyclotomicExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitKummerUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.GaloisNormLimitation

/-!
# Actual constant and S-unit Kummer extensions

Starting with an arbitrary prime-to-characteristic exponent, a finite constant
stage supplies the required roots of unity. Its inherited rational parameter
supplies the function-field structure. The actual S-unit root field over that
stage is finite abelian and has ramification confined to the chosen support.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [IsSepClosure K Ω]

/-- An actual finite constant extension supplies the roots of unity needed to
construct finite abelian S-unit root extensions with their proved ramification
bound. No primitive-root or function-field presentation is assumed over the
new base. The finite normal-closure construction also produces an actual
abelian extension over the original base with a smaller norm image. -/
theorem exists_constantStage_sUnitKummerExtension (n : ℕ+) [NeZero ((n : ℕ) : k)] :
    have _ : HasPrincipalDivisors k K := (isCurveOver k K).toHasPrincipalDivisors
    ∃ C : FiniteGaloisIntermediateField k Ω,
      let K' := constantExtensionStage (K := K) C.toIntermediateField
      let _ : IsScalarTower k K' Ω := IsScalarTower.to₁₃₄ k K K' Ω
      ∀ S : Finset (Place k K'), ∃ E : FiniteGaloisIntermediateField K' Ω,
        IsAbelianGalois K' E ∧
        E.toIntermediateField = SUnits.kummerExtension (Ω := Ω) n S ∧
        (∀ w : Place k E, w.restrict K' ∉ S → w.ramificationIndex K' = 1) ∧
        (let E₀ : IntermediateField K Ω := E.toIntermediateField.restrictScalars K
        let _ : Algebra K' E₀ := E.toIntermediateField.algebra
        have _ : IsScalarTower K K' E₀ :=
          IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext
            (IsScalarTower.algebraMap_apply K K' Ω x))
        have _ : FiniteDimensional K' E₀ := E.finiteDimensional
        have _ : FiniteDimensional K E₀ := Module.Finite.trans K' E₀
        have _ : HasPrincipalDivisors k E₀ :=
          (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E₀).toHasPrincipalDivisors
        ∃ A : FiniteGaloisIntermediateField K Ω, IsAbelianGalois K A ∧
          (have _ : HasPrincipalDivisors k A :=
            (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
              k K A).toHasPrincipalDivisors
          (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range ≤
            (IdeleClassGroup.norm (k := k) (K := K) (L := E₀)).range)) := by
  intro hKprincipal
  have hclosed : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨C, hmu⟩ := exists_constantStage_primitiveRoot k K Ω (n : ℕ)
  refine ⟨C, ?_⟩
  intro K' _ S
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K K'
  let aR : Algebra (RatFunc k) K' := presentation.val
  have hR : IsScalarTower k (RatFunc k) K' := presentation.property.1
  have hfunction : FunctionField k K' := presentation.property.2
  have hcurve : IsCurveOver k K' := isCurveOver k K'
  have hclosure : IsSepClosure K' Ω :=
    ⟨hclosed, Algebra.isSeparable_tower_top_of_isSeparable K K' Ω⟩
  have hn : ((n : ℕ) : K') ≠ 0 := by
    rw [← map_natCast (algebraMap k K')]
    exact (map_ne_zero (algebraMap k K')).mpr (NeZero.ne ((n : ℕ) : k))
  let E := SUnits.kummerExtension (Ω := Ω) n S
  have hfinite : FiniteDimensional K' E := SUnits.kummerExtension_finiteDimensional n hn hmu S
  have habelian : IsAbelianGalois K' E :=
    KummerTheory.kummerRadicalExtension_isAbelianGalois n hmu (SUnits.units k K' S)
  let Ef : FiniteGaloisIntermediateField K' Ω := { toIntermediateField := E }
  refine ⟨Ef, habelian, rfl,
    SUnits.kummerExtension_ramificationIndex_eq_one n hn hmu S, ?_⟩
  intro E₀ aK'E₀ hKEtower hK'E₀finite hE₀finite hE₀principal
  exact exists_finiteAbelian_norm_le k K Ω E₀

end FunctionField
