/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGalois
public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
public import Nyll.AlgebraicCurves.Places.ConstantExtension.RamificationIndexForgetConstantsEqOneAdjoinRangeEqTop
public import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Places in the full algebraic constant compositum

The constant extension is allowed to be infinite. Its actual constants generate
it as an algebra over every intermediate function field. This supplies the
integrality and unramifiedness needed to restrict a geometric place to a finite
constant stage. The resulting restriction preserves normalized orders and the
literal embedded residue values.
-/

@[expose] public section

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (C : IntermediateField k Ω) [Algebra.IsAlgebraic k C]

local notation "L" => IntermediateField.adjoin K (C : Set Ω)

local instance compositumConstants : Algebra C L := constantAlgebra (K := K) C

local instance compositumConstantTower : IsScalarTower k C L :=
  constantScalarTower (K := K) C

/-- Arbitrarily many algebraic constants generate their actual compositum as
an algebra, without a finite-dimensionality assumption on the constants. -/
theorem algebraicConstantExtension_adjoin_constants :
    Algebra.adjoin K (Set.range (algebraMap C L)) = ⊤ := by
  let iC : C →ₐ[k] L := constantEmbedding (K := K) C
  have himage : (IntermediateField.adjoin K (C : Set Ω)).val '' Set.range iC =
      (C : Set Ω) := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
      exact c.property
    · intro hx
      exact ⟨iC ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hfield : IntermediateField.adjoin K (Set.range iC) = ⊤ := by
    apply IntermediateField.map_injective (IntermediateField.adjoin K (C : Set Ω)).val
    rw [IntermediateField.adjoin_map, himage,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
    (F := K) (S := Set.range iC) ?_).mp hfield
  rintro x ⟨c, rfl⟩
  have hc : IsIntegral k (iC c) :=
    (Algebra.IsIntegral.isIntegral (R := k) c).map iC
  have hcK : IsIntegral K (iC c) := hc.tower_top
  exact hcK.isAlgebraic

variable (E : Type*) [Field E] [Algebra K E] [Algebra k E]
    [IsScalarTower k K E] [Algebra E (IntermediateField.adjoin K (C : Set Ω))]
    [IsScalarTower K E (IntermediateField.adjoin K (C : Set Ω))]
    [IsScalarTower k E (IntermediateField.adjoin K (C : Set Ω))]

omit [Algebra k E] [IsScalarTower k K E]
  [IsScalarTower k E (IntermediateField.adjoin K (C : Set Ω))] in
/-- The same actual constants generate the compositum over each intermediate
function field, with its given inclusion. -/
theorem algebraicConstantExtension_adjoin_over_intermediate :
    Algebra.adjoin E (Set.range (algebraMap C L)) = ⊤ := by
  let A : Subalgebra E L := Algebra.adjoin E (Set.range (algebraMap C L))
  have hle : Algebra.adjoin K (Set.range (algebraMap C L)) ≤ A.restrictScalars K :=
    Algebra.adjoin_le (R := K) (A := L) (S := A.restrictScalars K) (fun x hx =>
      show x ∈ Algebra.adjoin E (Set.range (algebraMap C L)) from
        Algebra.subset_adjoin hx)
  rw [algebraicConstantExtension_adjoin_constants (K := K) C] at hle
  apply top_unique
  intro x _
  exact hle Algebra.mem_top

omit [IsScalarTower k K E] in
/-- Integrality over an intermediate function field follows from the actual
algebraic constants and their proved algebra generation. -/
theorem algebraicConstantExtension_isIntegral_over_intermediate :
    Algebra.IsIntegral E L := by
  refine ⟨fun x => ?_⟩
  have hle : Algebra.adjoin E (Set.range (algebraMap C L)) ≤ integralClosure E L := by
    apply Algebra.adjoin_le
    rintro y ⟨c, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := k) c).map
      (IsScalarTower.toAlgHom k C L)).tower_top
  have hx : x ∈ Algebra.adjoin E (Set.range (algebraMap C L)) := by
    rw [algebraicConstantExtension_adjoin_over_intermediate (K := K) C E]
    exact Algebra.mem_top
  exact hle hx

/-- Restriction of a geometric place to the actual intermediate function
field; the required integrality is constructed from the constant compositum. -/
def algebraicConstantPlaceRestrict (W : Place C L) : Place k E := by
  let _ : Algebra.IsIntegral E L :=
    algebraicConstantExtension_isIntegral_over_intermediate (K := K) C E
  exact (W.forgetConstants (K := k)).restrict E

omit [IsScalarTower k K E] in
/-- The restricted place is the comap of the original valuation ring. -/
theorem algebraicConstantPlaceRestrict_toValuationSubring (W : Place C L) :
    (algebraicConstantPlaceRestrict (K := K) C E W).toValuationSubring =
      W.toValuationSubring.comap (algebraMap E L) := by
  let _ : Algebra.IsIntegral E L :=
    algebraicConstantExtension_isIntegral_over_intermediate (K := K) C E
  exact (W.forgetConstants (K := k)).restrict_toValuationSubring

/-- Restricting first to an intermediate function field and then to the
original function field gives the original direct geometric restriction. -/
theorem algebraicConstantPlaceRestrict_restrict [Algebra.IsIntegral K E]
    (W : Place C L) :
    (algebraicConstantPlaceRestrict (K := K) C E W).restrict K =
      algebraicConstantPlaceRestrict (K := K) C K W := by
  apply Place.ext
  rw [Place.restrict_toValuationSubring,
    algebraicConstantPlaceRestrict_toValuationSubring,
    algebraicConstantPlaceRestrict_toValuationSubring,
    ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq K E L]

variable [Algebra.IsSeparable k C]

omit [IsScalarTower k K E] in
/-- Every geometric place has ramification index one over its actual
intermediate function field, even for the full infinite constant extension. -/
theorem algebraicConstantPlaceRestrict_order (W : Place C L) (x : E) :
    W.ord (algebraMap E L x) =
      (algebraicConstantPlaceRestrict (K := K) C E W).ord x := by
  let _ : Algebra.IsIntegral E L :=
    algebraicConstantExtension_isIntegral_over_intermediate (K := K) C E
  have he := Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
    (K := k) (K' := C) (F := E) (F' := L)
    (algebraicConstantExtension_adjoin_over_intermediate (K := K) C E) W
  have ho := (W.forgetConstants (K := k)).ord_restrict (F := E) x
  rw [Place.ord_forgetConstants, he, Nat.cast_one, one_mul] at ho
  exact ho

omit [IsScalarTower k K E] in
/-- Literal residue values are preserved and reflected by the actual
geometric-to-finite-stage restriction. This includes the full principal-unit
condition by taking the value to be one. -/
theorem algebraicConstantPlaceRestrict_hasValue (W : Place C L) (x : E) (a : k) :
    W.HasValue (algebraMap E L x) (algebraMap k C a) ↔
      (algebraicConstantPlaceRestrict (K := K) C E W).HasValue x a := by
  let V := algebraicConstantPlaceRestrict (K := K) C E W
  have hcoeff : algebraMap C L (algebraMap k C a) =
      algebraMap E L (algebraMap k E a) := by
    exact (IsScalarTower.algebraMap_apply k C L a).symm.trans
      (IsScalarTower.algebraMap_apply k E L a)
  have hmem : algebraMap E L x ∈ W.toValuationSubring ↔
      x ∈ V.toValuationSubring := by
    rw [algebraicConstantPlaceRestrict_toValuationSubring]
    rfl
  have heq : algebraMap E L x = algebraMap C L (algebraMap k C a) ↔
      x = algebraMap k E a := by
    rw [hcoeff]
    exact (algebraMap E L).injective.eq_iff
  have hord : W.ord (algebraMap E L x - algebraMap C L (algebraMap k C a)) =
      V.ord (x - algebraMap k E a) := by
    rw [hcoeff, ← map_sub]
    exact algebraicConstantPlaceRestrict_order (K := K) C E W _
  rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos,
    Place.hasValue_iff_mem_and_eq_or_ord_sub_pos, hmem, heq, hord]

end FunctionField
