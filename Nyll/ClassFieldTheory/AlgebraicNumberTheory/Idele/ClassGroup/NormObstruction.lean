/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm

/-!
# The actual field-to-idele norm obstruction

For every finite extension of number fields the principal-idele map descends
from the field norm quotient to the quotient by the actual idele norm range.
Its kernel is the knot group. The extension degree annihilates this kernel,
by the existing scalar norm formula, without a Galois or cyclic assumption.
-/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

open scoped NumberField

noncomputable section

namespace NumberField.NormObstruction

open LocalFieldTheory.DiscreteValuationField

universe u v

variable (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The global-to-idele diagonal on the actual norm quotients. -/
noncomputable def hasseNormDiagonal :
    Kˣ ⧸ localNormSubgroup K L →*
      _root_.IdeleGroup K ⧸ (_root_.IdeleGroup.norm K L).range :=
  QuotientGroup.map (localNormSubgroup K L) (_root_.IdeleGroup.norm K L).range
    (_root_.IdeleGroup.principalIdele K) (by
      rintro _ ⟨y, rfl⟩
      exact ⟨_root_.IdeleGroup.principalIdele L y, _root_.IdeleGroup.norm_principalIdele K L y⟩)

/-- The actual diagonal sends a field-unit class to its principal-idele class. -/
@[simp]
theorem hasseNormDiagonal_mk (x : Kˣ) :
    hasseNormDiagonal K L (QuotientGroup.mk' (localNormSubgroup K L) x) =
      QuotientGroup.mk' (_root_.IdeleGroup.norm K L).range (_root_.IdeleGroup.principalIdele K x) :=
  rfl

/-- The knot group is the kernel of the actual norm diagonal. -/
abbrev Knot := (hasseNormDiagonal K L).ker

/-- A field-unit class is an obstruction precisely when its principal idele is
an actual idele norm. -/
theorem mk_mem_knot_iff (x : Kˣ) :
    QuotientGroup.mk' (localNormSubgroup K L) x ∈ Knot K L ↔
      _root_.IdeleGroup.principalIdele K x ∈ (_root_.IdeleGroup.norm K L).range :=
  QuotientGroup.eq_one_iff (_root_.IdeleGroup.principalIdele K x)

/-- The degree annihilates every norm obstruction; this asserts bounded
exponent, not finiteness of the norm quotient or its kernel. -/
theorem knot_pow_finrank_eq_one (q : Knot K L) :
    q ^ Module.finrank K L = 1 := by
  apply Subtype.ext
  exact fieldNormQuotient_pow_finrank_eq_one K L q.1

/-- Vanishing of the actual norm obstruction is exactly the actual
principal-idele local-to-global norm implication. -/
theorem hasseNormDiagonal_injective_iff :
    Function.Injective (hasseNormDiagonal K L) ↔
      (_root_.IdeleGroup.norm K L).range.comap (_root_.IdeleGroup.principalIdele K) ≤
        localNormSubgroup K L := by
  constructor
  · intro hinj x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply hinj
    rw [map_one]
    exact (hasseNormDiagonal_mk K L x).trans
      ((QuotientGroup.eq_one_iff (_root_.IdeleGroup.principalIdele K x)).mpr hx)
  · intro hnorm
    apply (MonoidHom.ker_eq_bot_iff (f := hasseNormDiagonal K L)).mp
    apply le_antisymm
    · intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (localNormSubgroup K L) q
      change QuotientGroup.mk' (localNormSubgroup K L) x = 1
      exact (QuotientGroup.eq_one_iff x).mpr
        (hnorm ((mk_mem_knot_iff K L x).mp hq))
    · exact bot_le

end NumberField.NormObstruction
