/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegPos
import Nyll.AlgebraicCurves.Places.Residue.ResidueFieldEqCompositum
import Nyll.GaloisCohomology.FieldTheory.FiniteCompositumDegree

/-!
# Residue degrees in finite constant extensions

The residue field of a constant extension is the compositum of the new
constants and the original residue field. Over finite constants its degree is
therefore the least common multiple of their degrees. The residue extension
degree is the constant degree divided by its gcd with the degree of the place.
-/

noncomputable section

namespace AlgebraicCurve.Place

variable {k C K E : Type*} [Field k] [Finite k] [Field C] [Field K] [Field E]
    [Algebra k C] [Algebra k K] [Algebra k E] [Algebra C E] [Algebra K E]
    [IsScalarTower k C E] [IsScalarTower k K E]
    [FiniteDimensional k C] [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [IsCurveOver k K]

/-- The residue degree in a finite constant compositum is the lcm of the
constant degree and the degree of the original place. -/
theorem deg_forgetConstants_eq_lcm
    (hgen : Algebra.adjoin K (Set.range (algebraMap C E)) = ⊤) (W : Place C E) :
    (W.forgetConstants (K := k)).deg =
      Nat.lcm (Module.finrank k C) ((W.forgetConstants (K := k)).restrict K).deg := by
  let w := W.forgetConstants (K := k)
  let v := w.restrict K
  have : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  have : Finite v.ResidueField := Module.finite_of_finite k
  have : Module.Finite v.ResidueField w.ResidueField :=
    Module.finite_of_finrank_pos (w.inertiaDeg_pos (F := K))
  have : Finite w.ResidueField := Module.finite_of_finite v.ResidueField
  let : Algebra C w.ResidueField := (inferInstance : Algebra C W.ResidueField)
  let : Algebra k W.toValuationSubring :=
    (inferInstance : Algebra k w.toValuationSubring)
  have : IsScalarTower k C W.toValuationSubring :=
    IsScalarTower.of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k C E x)
  have hres : IsScalarTower k C W.ResidueField := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply k W.toValuationSubring W.ResidueField,
      IsScalarTower.algebraMap_apply C W.toValuationSubring W.ResidueField,
      IsScalarTower.algebraMap_apply k C W.toValuationSubring]
  have : IsScalarTower k C w.ResidueField := hres
  let iC := IsScalarTower.toAlgHom k C w.ResidueField
  let iV := IsScalarTower.toAlgHom k v.ResidueField w.ResidueField
  let A := iC.fieldRange
  let B := iV.fieldRange
  have hsup : A ⊔ B = ⊤ := by
    let T : IntermediateField C w.ResidueField :=
      { (A ⊔ B).toSubfield with
        algebraMap_mem' := fun x => (show A ≤ A ⊔ B from le_sup_left) ⟨x, rfl⟩ }
    have hle : IntermediateField.adjoin C (Set.range (w.restrictResidueMap K)) ≤ T := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro x ⟨y, rfl⟩
      exact (show B ≤ A ⊔ B from le_sup_right) ⟨y, rfl⟩
    have htop : IntermediateField.adjoin C (Set.range (w.restrictResidueMap K)) = ⊤ :=
      residueField_eq_compositum_of_isConstantFieldExtension hgen W
    rw [htop] at hle
    apply top_unique
    intro x _
    exact hle IntermediateField.mem_top
  have hdegree := FiniteField.finrank_eq_lcm_of_sup_eq_top A B hsup
  rw [← iC.equivFieldRange.toLinearEquiv.finrank_eq,
    ← iV.equivFieldRange.toLinearEquiv.finrank_eq] at hdegree
  exact hdegree

/-- The residue extension degree in a finite constant compositum is the
constant degree divided by its gcd with the degree of the original place. -/
theorem inertiaDeg_forgetConstants_eq_div_gcd
    (hgen : Algebra.adjoin K (Set.range (algebraMap C E)) = ⊤) (W : Place C E) :
    (W.forgetConstants (K := k)).inertiaDeg K =
      Module.finrank k C /
        Nat.gcd (Module.finrank k C) ((W.forgetConstants (K := k)).restrict K).deg := by
  let w := W.forgetConstants (K := k)
  let d := (w.restrict K).deg
  let n := Module.finrank k C
  have : Module.Finite k (w.restrict K).ResidueField :=
    IsCurveOver.finiteResidue (w.restrict K)
  have hd : 0 < d := Module.finrank_pos
  have hmul : d * w.inertiaDeg K = Nat.lcm n d :=
    (w.deg_restrict_mul_inertiaDeg (F := K)).trans (deg_forgetConstants_eq_lcm hgen W)
  have hgcd : Nat.gcd n d * w.inertiaDeg K = n := by
    apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * (Nat.gcd n d * w.inertiaDeg K) = Nat.gcd n d * (d * w.inertiaDeg K) :=
        by ring
      _ = Nat.gcd n d * Nat.lcm n d := by rw [hmul]
      _ = n * d := Nat.gcd_mul_lcm n d
      _ = d * n := Nat.mul_comm n d
  exact (Nat.div_eq_of_eq_mul_right (Nat.gcd_pos_of_pos_right n hd) hgcd.symm).symm

end AlgebraicCurve.Place
