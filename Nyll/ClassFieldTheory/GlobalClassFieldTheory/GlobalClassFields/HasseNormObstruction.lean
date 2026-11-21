/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormObstruction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple

/-!
# The actual norm obstruction and the cyclic Hasse theorem

The older local-condition quotient and the actual idele norm quotient agree
for finite Galois extensions by the existing restricted-product norm theorem.
Their diagonals agree on principal representatives. Thus the existing cyclic
Hasse theorem kills the kernel of the actual diagonal introduced without a
Galois assumption.
-/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

universe u v

variable (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Ordinary and relative ideles have the same norm range, hence the same
all-place local norm condition for a finite Galois extension. -/
theorem ideleNorm_range_eq_allPlaceLocalNormCondition :
    (IdeleGroup.norm K L).range = allPlaceLocalNormCondition (K := K) (L := L) := by
  exact (IdeleGroup.norm_range_eq_relativeNorm_range K L).trans
    (relativeIdeleNorm_range_eq_allPlaceLocalNormCondition (K := K) (L := L))

/-- The actual norm quotient and the local-condition quotient use the same
idele representatives. -/
noncomputable def actualIdeleNormQuotientEquivLocalCondition :
    IdeleGroup K ⧸ (IdeleGroup.norm K L).range ≃*
      IdeleGroup K ⧸ allPlaceLocalNormCondition (K := K) (L := L) :=
  QuotientGroup.quotientMulEquivOfEq
    (ideleNorm_range_eq_allPlaceLocalNormCondition K L)

/-- The comparison of norm quotients commutes with the principal-idele diagonal. -/
theorem actualHasseNormDiagonal_comparison
    (q : Kˣ ⧸ localNormSubgroup K L) :
    actualIdeleNormQuotientEquivLocalCondition K L
        (NumberField.NormObstruction.hasseNormDiagonal K L q) =
      hasseNormDiagonal K L q := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (localNormSubgroup K L) q
  rw [NumberField.NormObstruction.hasseNormDiagonal_mk]
  exact QuotientGroup.quotientMulEquivOfEq_mk
    (ideleNorm_range_eq_allPlaceLocalNormCondition K L) (IdeleGroup.principalIdele K x)

/-- The existing cyclic Hasse theorem makes the actual norm diagonal injective. -/
theorem actualHasseNormDiagonal_injective_cyclic [IsCyclic (L ≃ₐ[K] L)] :
    Function.Injective (NumberField.NormObstruction.hasseNormDiagonal K L) := by
  intro a b hab
  apply hasseNormDiagonal_injective_cyclic K L
  rw [← actualHasseNormDiagonal_comparison K L a,
    ← actualHasseNormDiagonal_comparison K L b, hab]

/-- The actual knot subgroup is trivial for a cyclic extension. -/
theorem knot_eq_bot_cyclic [IsCyclic (L ≃ₐ[K] L)] :
    NumberField.NormObstruction.Knot K L = ⊥ :=
  (MonoidHom.ker_eq_bot_iff
    (f := NumberField.NormObstruction.hasseNormDiagonal K L)).mpr
    (actualHasseNormDiagonal_injective_cyclic K L)

end GlobalClassFieldTheory.ClassFieldAxiom
