/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.UnramifiedNormalization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap

/-!
# Arithmetic Frobenius at an unramified finite place

The pre-existing local class-formation coordinate has geometric
Frobenius normalization.  This file supplies the canonical prime Artin
element used in the ideal-theoretic formulation: the ordinary normalized
prime idèle maps to arithmetic Frobenius.
-/



@[expose] public section

open scoped NumberField

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The arithmetic global Artin element of the ordinary normalized
one-place prime idèle. -/
noncomputable def arithmeticFinitePlacePrimeArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    L ≃ₐ[K] L :=
  Reciprocity.arithmeticGlobalArtinMonoidHom K L
    (finitePrimeIdele v)

/-- The arithmetic prime Artin element is the arithmetic chosen local
Artin value of the normalized order-one element. -/
@[simp]
theorem arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
        K L v (FiniteIdeleGroup.chosenLocalOrderSection v 1) := by
  rw [arithmeticFinitePlacePrimeArtin, finitePrimeIdele,
    Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele]

/-- The arithmetic prime Artin value is the global norm-residue value of
the same normalized prime idèle class, in independent field universes. -/
theorem arithmeticFinitePlacePrimeArtin_eq_arithmeticGlobalNormResidue
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      Reciprocity.arithmeticGlobalNormResidueMonoidHom K L
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v)) := by
  rw [arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin]
  exact (DFunLike.congr_fun
    (Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
      K L v) (FiniteIdeleGroup.chosenLocalOrderSection v 1)).symm

/-- Arithmetic and geometric prime Artin elements are inverse
automorphisms. -/
@[simp]
theorem arithmeticFinitePlacePrimeArtin_eq_inv
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      (finitePlacePrimeArtin (K := K) (L := L) v)⁻¹ := by
  rw [arithmeticFinitePlacePrimeArtin,
    Reciprocity.arithmeticGlobalArtinMonoidHom_apply,
    finitePlacePrimeArtin]

/-- The arithmetic Frobenius of the actual chosen completed extension,
transported through its decomposition group into the global Galois group.
The unramifiedness hypothesis concerns this chosen extension, not an
unrelated abstract local field. -/
noncomputable def chosenFinitePlaceArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    L ≃ₐ[K] L := by
  let w := chosenFinitePlaceExtension (L := L) v
  exact Reciprocity.finitePlaceLocalToGlobalMonoidHom
    (K := K) (L := L) v w
    (Reciprocity.chosenFinitePlaceLocalArithmeticFrobenius
      (K := K) (L := L) v hunram)

/-- At an unramified chosen finite place, the arithmetic prime Artin
element really is the global decomposition-group transport of local
arithmetic Frobenius. The local input has valuation `-1` in the
construction's convention, and arithmetic global reciprocity inverts
that geometric local Artin value. -/
theorem arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hunram := by
  let w := chosenFinitePlaceExtension (L := L) v
  let x : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  have hgeometric :
      Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x =
        (chosenFinitePlaceArithmeticFrobenius
          (K := K) (L := L) v hunram)⁻¹ := by
    change Reciprocity.finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x = _
    rw [Reciprocity.finitePlaceArtinMonoidHomOfExtension_factor]
    change Reciprocity.finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (Reciprocity.finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x) = _
    rw [Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified
      (K := K) (L := L) v hunram, map_inv]
    rfl
  rw [arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin,
    Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply]
  rw [hgeometric, inv_inv]

/-- At an unramified chosen place, the arithmetic prime Artin element
has order equal to the local extension degree. -/
theorem
    orderOf_arithmeticFinitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    orderOf
        (arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) =
      _root_.finitePlaceLocalDegree
        (K := K) (L := L) v := by
  rw [arithmeticFinitePlacePrimeArtin_eq_inv,
    orderOf_inv]
  exact
    orderOf_finitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
      (K := K) (L := L) v hunram

/-- An unramified finite place splits completely exactly when its
arithmetic Frobenius is trivial. -/
theorem
    arithmeticFinitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v =
        1 ↔
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  rw [arithmeticFinitePlacePrimeArtin_eq_inv, inv_eq_one]
  exact
    finitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified
      (K := K) (L := L) v hunram

end GlobalClassFields
end GlobalClassFieldTheory
