/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
import Nyll.AlgebraicCurves.Places.Ramification.NcardAlgHomCompEqPreimageEqRamificationIndex

/-!
# Actual divisor and Picard pullbacks in constant towers

Restriction of places composes along the given field tower. The proved
multiplicativity of ramification indices then identifies the two actual
divisor pullbacks and their induced Picard maps.
-/

noncomputable section

namespace AlgebraicCurve

open AlgebraicCurves.Places.Proofs
open Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.AlgebraicCurve

variable {k E Ω K L M : Type*} [Field k] [Field E] [Field Ω]
    [Field K] [Field L] [Field M]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω]
    [Algebra k K] [Algebra k L] [Algebra E L] [IsScalarTower k E L]
    [Algebra k M] [Algebra E M] [Algebra Ω M]
    [IsScalarTower k Ω M] [IsScalarTower E Ω M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower E L M] [IsScalarTower K L M]
    [Algebra.IsIntegral K L] [Algebra.IsIntegral L M] [Algebra.IsIntegral K M]

omit [IsScalarTower k L M] in
/-- Restricting both function fields and constants in a tower agrees with direct restriction. -/
theorem Place.restrictConstants_tower (w : Place Ω M) :
    Place.restrictConstants K (K := k) (Place.restrictConstants L (K := E) w) =
      Place.restrictConstants K (K := k) w := by
  apply Place.ext
  change (w.toValuationSubring.comap (algebraMap L M)).comap (algebraMap K L) =
    w.toValuationSubring.comap (algebraMap K M)
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq K L M]

/-- Actual ramification indices multiply across simultaneous constant and function-field towers. -/
theorem Place.ramificationIndex_constantTower (w : Place Ω M) :
    (w.forgetConstants (K := k)).ramificationIndex K =
      (w.forgetConstants (K := E)).ramificationIndex L *
        ((Place.restrictConstants L (K := E) w).forgetConstants (K := k)).ramificationIndex K := by
  have h := SpecialisationCount.ramificationIndex_tower
    (F := K) (F' := L) (w.forgetConstants (K := k))
  have hw : (w.forgetConstants (K := k)).restrict L =
      (Place.restrictConstants L (K := E) w).forgetConstants (K := k) := Place.ext rfl
  rw [hw] at h
  exact h

variable [HasPrincipalDivisors E L] [HasPrincipalDivisors Ω M]

/-- The actual constant-extension divisor pullbacks compose along the field tower. -/
theorem Divisor.pullbackConstants_tower (D : Divisor k K) :
    Divisor.pullbackConstants Ω M (Divisor.pullbackConstants E L D) =
      Divisor.pullbackConstants Ω M D := by
  ext w
  rw [Divisor.pullbackConstants_apply, Divisor.pullbackConstants_apply,
    Divisor.pullbackConstants_apply, Place.restrictConstants_tower,
    Place.ramificationIndex_constantTower (k := k) (E := E) (K := K) (L := L) w,
    Nat.cast_mul, mul_assoc]

/-- The actual Picard base-change maps compose along the same field tower. -/
theorem Pic.baseChange_tower (x : Pic k K) :
    Pic.baseChange E Ω L M (Pic.baseChange k E K L x) = Pic.baseChange k Ω K M x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  change H1Gm.mk (Divisor.pullbackConstants Ω M (Divisor.pullbackConstants E L D)) =
    H1Gm.mk (Divisor.pullbackConstants Ω M D)
  rw [Divisor.pullbackConstants_tower]

end AlgebraicCurve
