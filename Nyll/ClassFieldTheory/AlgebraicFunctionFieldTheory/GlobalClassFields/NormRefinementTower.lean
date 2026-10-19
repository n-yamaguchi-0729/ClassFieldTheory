/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.GaloisNormLimitation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormAlgEquiv
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Actual abelian norm refinement down a tower

Compose actual norms, regard a relative finite extension as an intermediate
field over the original base, and apply the existing normal-closure
abelian refinement. The two norm groups are identified by an explicit
algebra equivalence before the refinement.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [IsSepClosure K Ω]

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
private theorem norm_range_le_of_tower
    {L M : Type} [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
    [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]
    (H : Subgroup (IdeleClassGroup k K))
    (h : (IdeleClassGroup.norm (k := k) (K := L) (L := M)).range ≤
      H.comap (IdeleClassGroup.norm (k := k) (K := K) (L := L))) :
    have _ : FiniteDimensional K M := Module.Finite.trans L M
    have _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    (IdeleClassGroup.norm (k := k) (K := K) (L := M)).range ≤ H := by
  intro hfinite hseparable
  rintro c ⟨d, rfl⟩
  rw [← IdeleClassGroup.norm_trans (k := k) (K := K) (L := L) (M := M) d]
  exact h ⟨d, rfl⟩

/-- A finite relative extension with sufficiently small actual norm image
gives an actual finite abelian extension over the original base. -/
theorem exists_finiteAbelian_norm_le_of_relative
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [HasPrincipalDivisors k L] (H : Subgroup (IdeleClassGroup k K)) :
    have _ : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
    ∀ E : FiniteGaloisIntermediateField L Ω,
      (have _ : HasPrincipalDivisors k E :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k L E).toHasPrincipalDivisors
      (IdeleClassGroup.norm (k := k) (K := L) (L := E)).range ≤
        H.comap (IdeleClassGroup.norm (k := k) (K := K) (L := L))) →
      ∃ A : FiniteGaloisIntermediateField K Ω, IsAbelianGalois K A ∧
        (have _ : HasPrincipalDivisors k A :=
          (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K A).toHasPrincipalDivisors
        (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range ≤ H) := by
  intro hkLΩ E hEnorm
  have hKLE : IsScalarTower K L E := IntermediateField.isScalarTower E.toIntermediateField
  have hkKE : IsScalarTower k K E :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext
      (IsScalarTower.algebraMap_apply k K Ω x))
  have hKEfinite : FiniteDimensional K E := Module.Finite.trans L E
  have hKEsep : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K L E
  have hEprincipal : HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k L E).toHasPrincipalDivisors
  have hnorm : (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range ≤ H :=
    norm_range_le_of_tower k K (L := L) (M := E) H hEnorm
  let E₀ : IntermediateField K Ω := E.toIntermediateField.restrictScalars K
  let φ : E ≃ₐ[K] E₀ :=
    { RingEquiv.refl E with commutes' := fun _ => rfl }
  have hE₀finite : FiniteDimensional K E₀ := φ.toLinearEquiv.finiteDimensional
  have hE₀principal : HasPrincipalDivisors k E₀ :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E₀).toHasPrincipalDivisors
  have hnormEq := IdeleClassGroup.norm_range_eq_of_algEquiv (k := k) (K := K) φ
  obtain ⟨A, hA, hAN⟩ := exists_finiteAbelian_norm_le k K Ω E₀
  exact ⟨A, hA, hAN.trans (hnormEq.symm.le.trans hnorm)⟩

end FunctionField
