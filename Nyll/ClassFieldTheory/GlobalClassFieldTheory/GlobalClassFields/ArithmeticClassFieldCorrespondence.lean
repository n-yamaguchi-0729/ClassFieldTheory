/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

/-!
# Arithmetic topological class-field correspondence

For a closed finite-index subgroup `H ≤ C_K`, the selected actual
class field has norm range exactly `H`.  This module records the
canonical arithmetic reciprocity homeomorphism
`Gal(L/K) ≃ₜ* C_K/H`, so both the field and the topological group map
are fixed rather than merely asserted to exist.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

universe u v

variable {K : Type u} [Field K] [NumberField K]


/-- Arithmetic global reciprocity for the actual class field selected
by a closed finite-index idèle-class subgroup. -/
noncomputable def
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Gal((closedFiniteIndexClassField
          (K := K) H hclosed) / K) ≃ₜ*
      IdeleClassGroup K ⧸ H :=
  (arithmeticGlobalReciprocityContinuousMulEquiv K
    (closedFiniteIndexClassField (K := K) H hclosed)).trans
    (QuotientGroup.quotientContinuousMulEquivOfEq
      (closedFiniteIndexClassField_ideleClassNorm_range (K := K) H hclosed))

private theorem arithmeticReciprocity_trans_quotient_apply
    {L : Type v} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {H : Subgroup (IdeleClassGroup K)} (hNorm : (_root_.ideleClassNorm K L).range = H)
    (c : IdeleClassGroup K) :
    ((arithmeticGlobalReciprocityContinuousMulEquiv K L).trans
      (QuotientGroup.quotientContinuousMulEquivOfEq hNorm))
        (arithmeticGlobalNormResidueMonoidHom K L c) = QuotientGroup.mk' H c := by
  let q := QuotientGroup.quotientContinuousMulEquivOfEq hNorm
  calc
    _ = q (arithmeticGlobalReciprocityContinuousMulEquiv K L
        (arithmeticGlobalNormResidueMonoidHom K L c)) := rfl
    _ = q (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c) :=
      congrArg q (arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue K L c)
    _ = QuotientGroup.quotientMulEquivOfEq hNorm
        (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c) :=
      QuotientGroup.quotientContinuousMulEquivOfEq_apply _ _
    _ = QuotientGroup.mk' H c := QuotientGroup.quotientMulEquivOfEq_mk hNorm c

/-- The arithmetic norm-residue symbol of an idèle class maps to its
literal class modulo the defining subgroup. -/
@[simp]
theorem
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient_globalNormResidue
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (c : IdeleClassGroup K) :
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
        (K := K) H hclosed
        (arithmeticGlobalNormResidueMonoidHom K
          (closedFiniteIndexClassField
            (K := K) H hclosed) c) =
      QuotientGroup.mk' H c := by
  exact arithmeticReciprocity_trans_quotient_apply
    (K := K) (L := closedFiniteIndexClassField (K := K) H hclosed)
    (closedFiniteIndexClassField_ideleClassNorm_range (K := K) H hclosed) c

/-- The inverse correspondence sends a represented class modulo `H`
to its actual arithmetic global norm-residue automorphism. -/
@[simp]
theorem
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient_symm_mk
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (c : IdeleClassGroup K) :
    (arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
      (K := K) H hclosed).symm
        (QuotientGroup.mk' H c) =
      arithmeticGlobalNormResidueMonoidHom K
        (closedFiniteIndexClassField
          (K := K) H hclosed) c := by
  apply (arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
    (K := K) H hclosed).symm_apply_eq.mpr
  exact (arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient_globalNormResidue
    (K := K) H hclosed c).symm

end GlobalClassFields
end GlobalClassFieldTheory
