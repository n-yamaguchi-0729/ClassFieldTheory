/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormAlgEquiv

/-!
# Norm limitation for an actual finite Galois extension

Restriction from the full Galois group to the fixed field of its commutator
induces an isomorphism on abelianizations. Finite reciprocity and its actual
norm kernel therefore identify the two idele-class norm images.
-/

noncomputable section

namespace FunctionField

open scoped IsMulCommutative

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Passing from a finite Galois extension to its actual maximal abelian
subfield preserves the full idele-class norm image. -/
theorem finiteGalois_norm_range_eq_commutatorFixedField :
    let A : IntermediateField K L := IntermediateField.fixedField (commutator Gal(L/K))
    have _ : IsGalois K A :=
      IsGalois.of_fixedField_normal_subgroup (commutator Gal(L/K))
    have _ : AlgebraicCurve.HasPrincipalDivisors k A :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K A).toHasPrincipalDivisors
    (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range =
      (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range := by
  intro A hAgal hAprincipal
  let e : Abelianization Gal(L/K) ≃* Gal(A/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(L/K))
  have hcomm : IsMulCommutative Gal(A/K) :=
    e.surjective.isMulCommutative inferInstance
  let r : Gal(L/K) →* Gal(A/K) := AlgEquiv.restrictNormalHom A
  have hmap (z : Abelianization Gal(L/K)) :
      Abelianization.map r z = Abelianization.of (e z) := by
    refine QuotientGroup.induction_on z ?_
    intro σ
    change Abelianization.map r (Abelianization.of σ) =
      Abelianization.of (e (Abelianization.of σ))
    rw [Abelianization.map_of]
    apply congrArg Abelianization.of
    exact (IsGalois.normalAutEquivQuotient_apply (commutator Gal(L/K)) σ).symm
  have hinjective : Function.Injective (Abelianization.map r) := by
    intro x y hxy
    apply e.injective
    apply (Abelianization.equivOfComm (H := Gal(A/K))).injective
    exact (hmap x).symm.trans (hxy.trans (hmap y))
  apply Subgroup.ext
  intro c
  rw [← finiteArtin_eq_one_iff_mem_norm k K L c,
    ← finiteArtin_eq_one_iff_mem_norm k K A c]
  have hrestriction := finiteArtin_restrictNormal k K A L c
  constructor
  · intro hc
    rw [← hrestriction, hc, map_one]
  · intro hc
    apply hinjective
    exact hrestriction.trans (hc.trans (map_one (Abelianization.map r)).symm)

/-- Every finite subextension of the fixed Galois overfield admits an actual
finite abelian subextension in the same overfield whose norm image is smaller.
The field is the embedded commutator fixed field of the finite normal closure. -/
theorem exists_finiteAbelian_norm_le
    (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsGalois K Ω] (E : IntermediateField K Ω) [FiniteDimensional K E] :
    have _ : AlgebraicCurve.HasPrincipalDivisors k E :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
    ∃ A : FiniteGaloisIntermediateField K Ω,
      IsAbelianGalois K A ∧
        (have _ : AlgebraicCurve.HasPrincipalDivisors k A :=
          (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K A).toHasPrincipalDivisors
        (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range ≤
          (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range) := by
  intro hEprincipal
  let M : IntermediateField K Ω := IntermediateField.normalClosure K E Ω
  have hkEM : IsScalarTower k E M := IsScalarTower.to₁₃₄ k K E M
  have hEMfinite : FiniteDimensional E M := FiniteDimensional.right K E M
  have hEMseparable : Algebra.IsSeparable E M :=
    Algebra.isSeparable_tower_top_of_isSeparable K E M
  have hMprincipal : AlgebraicCurve.HasPrincipalDivisors k M :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K M).toHasPrincipalDivisors
  let A : IntermediateField K M := IntermediateField.fixedField (commutator Gal(M/K))
  have hAgal : IsGalois K A :=
    IsGalois.of_fixedField_normal_subgroup (commutator Gal(M/K))
  let e : Abelianization Gal(M/K) ≃* Gal(A/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(M/K))
  have hcomm : IsMulCommutative Gal(A/K) :=
    e.surjective.isMulCommutative inferInstance
  have hAabelian : IsAbelianGalois K A :=
    { toIsGalois := hAgal, toIsMulCommutative := hcomm }
  have hAprincipal : AlgebraicCurve.HasPrincipalDivisors k A :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K A).toHasPrincipalDivisors
  let B : IntermediateField K Ω := A.map M.val
  let φ : A ≃ₐ[K] B := A.equivMap M.val
  have hBfinite : FiniteDimensional K B := φ.toLinearEquiv.finiteDimensional
  have hBabelian : IsAbelianGalois K B := IsAbelianGalois.of_algHom φ.symm.toAlgHom
  let Bf : FiniteGaloisIntermediateField K Ω := { toIntermediateField := B }
  refine ⟨Bf, hBabelian, ?_⟩
  intro hBprincipal
  change (IdeleClassGroup.norm (k := k) (K := K) (L := B)).range ≤
    (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range
  calc
    (IdeleClassGroup.norm (k := k) (K := K) (L := B)).range =
        (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range :=
      (IdeleClassGroup.norm_range_eq_of_algEquiv (k := k) φ).symm
    _ = (IdeleClassGroup.norm (k := k) (K := K) (L := M)).range :=
      (finiteGalois_norm_range_eq_commutatorFixedField k K M).symm
    _ ≤ (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range := by
      rintro c ⟨d, rfl⟩
      exact ⟨IdeleClassGroup.norm (k := k) (K := E) (L := M) d,
        IdeleClassGroup.norm_trans (k := k) (K := K) (L := E) (M := M) d⟩

end FunctionField
