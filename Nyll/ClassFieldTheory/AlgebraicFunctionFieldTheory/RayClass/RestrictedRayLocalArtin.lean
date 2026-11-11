/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayProduct
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.FiniteArtin
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalConductor
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalDecomposition

/-!
# Original local Artin maps on the restricted ray product

For every actual finite abelian extension with conductor bounded by the modulus,
its finite Artin map acts on the local restricted product. A local ray factor
surjects onto the original decomposition group, with the original norm kernel.
Outside the boundary the one-place symbol is precisely the normalized integer
power of the arithmetic residue Frobenius.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField.RayClass

open AlgebraicCurve

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The existing finite Artin map, on the actual restricted product of local ray factors. -/
def restrictedProductFiniteArtin (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) :
    RayRestrictedProduct m →* Gal(L/K) :=
  (rayClassArtin k K L m hm).comp (restrictedProductToRayClass m)

/-- The restricted-product map uses the original finite Artin value of every idele. -/
theorem restrictedProductFiniteArtin_idele (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (a : IdeleGroup k K) :
    restrictedProductFiniteArtin m hm (ideleToRayRestrictedProduct m a) =
      abelianFiniteArtin k K L (IdeleClassGroup.mk a) := by
  have he : rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) a) =
      ideleToRayRestrictedProduct m a := rfl
  rw [← he]
  change rayClassArtin k K L m hm (localToRayClass m ((rayLocalRestrictedProductEquiv m).symm
    (rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) a)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The conductor bound places the prescribed local higher units in the local Artin kernel. -/
theorem localHigherUnitGroup_le_localDecompositionArtin_ker
    (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L) :
    localHigherUnitGroup (w.restrict K) (m (w.restrict K)) ≤
      (localDecompositionArtin (K := K) w).toMonoidHom.ker := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  have hbound := (extensionConductor_le_iff_localConductor (L := L) m).mp hm w
  have hcriterion := localConductorExponent_le_iff_localArtin (K := K) w (m (w.restrict K))
  dsimp only at hbound hcriterion
  intro x hx
  change localDecompositionArtin (K := K) w x = 1
  apply Subtype.ext
  exact hcriterion.mp hbound x hx

/-- The actual local ray factor maps into the original finite decomposition group. -/
def localRayDecompositionArtin (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L) :
    RayLocalFactor m (w.restrict K) →* IdeleGroup.decompositionGroup (K := K) w :=
  QuotientGroup.lift (localHigherUnitGroup (w.restrict K) (m (w.restrict K)))
    (localDecompositionArtin (K := K) w).toMonoidHom
    (localHigherUnitGroup_le_localDecompositionArtin_ker m hm w)

/-- Its representatives are evaluated by the original local reciprocity map. -/
theorem localRayDecompositionArtin_mk (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    localRayDecompositionArtin m hm w
      (QuotientGroup.mk' (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) x) =
        localDecompositionArtin (K := K) w x := rfl

/-- Every original decomposition automorphism is reached by its actual local ray factor. -/
theorem localRayDecompositionArtin_surjective (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L) :
    Function.Surjective (localRayDecompositionArtin m hm w) := by
  intro σ
  obtain ⟨x, hx⟩ := localDecompositionArtin_surjective (K := K) w σ
  exact ⟨QuotientGroup.mk x, hx⟩

/-- The local ray kernel is the image of the genuine completed field-norm group. -/
theorem localRayDecompositionArtin_ker (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L) :
    (localRayDecompositionArtin m hm w).ker =
      (IdeleGroup.localNorm (K := K) w).range.map
        (QuotientGroup.mk' (localHigherUnitGroup (w.restrict K) (m (w.restrict K)))) := by
  change (QuotientGroup.lift (localHigherUnitGroup (w.restrict K) (m (w.restrict K)))
    (localDecompositionArtin (K := K) w).toMonoidHom
    (localHigherUnitGroup_le_localDecompositionArtin_ker m hm w)).ker = _
  rw [QuotientGroup.ker_lift, localDecompositionArtin_ker]

/-- The restricted-product symbol at one place is the original global-valued local symbol. -/
theorem restrictedProductFiniteArtin_placeIdele (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    restrictedProductFiniteArtin m hm
      (ideleToRayRestrictedProduct m (IdeleGroup.placeIdele (w.restrict K) x)) =
        localArtin (K := K) w x := by
  rw [restrictedProductFiniteArtin_idele]
  exact (localArtin_eq_abelianFiniteArtin_placeIdele k K L w x).symm

/-- Away from the actual modulus, the local symbol is the normalized order
power of the original arithmetic residue Frobenius. -/
theorem restrictedProductFiniteArtin_placeIdele_frobenius (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L)
    (hw : w.restrict K ∉ m.support) (x : (w.restrict K).adicCompletionˣ) :
    restrictedProductFiniteArtin m hm
      (ideleToRayRestrictedProduct m (IdeleGroup.placeIdele (w.restrict K) x)) =
        (unramifiedDecompositionFrobenius (K := K) w
          (ramificationIndex_eq_one_of_not_mem_support m hm w hw)).val ^
            (IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  rw [restrictedProductFiniteArtin_idele]
  exact abelianFiniteArtin_placeIdele_eq_unramifiedFrobenius_zpow w
    (ramificationIndex_eq_one_of_not_mem_support m hm w hw) x

end FunctionField.RayClass
