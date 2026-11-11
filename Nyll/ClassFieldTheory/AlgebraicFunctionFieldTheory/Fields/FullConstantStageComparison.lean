/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.FiniteConstantFieldIso
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Literal constant stages when the original base is the full constants

Finite constant subfields in an ambient field are independent of the
embedding: their images are determined by their cardinality. If the given
finite base is already the full constants of the original function field,
the existing full-constant degree stage is therefore the literal
compositum with the degree stage over that original base.
-/

@[expose] public section

noncomputable section

namespace FunctionField

section FiniteConstants

variable (k κ Ω : Type*) [Field k] [Finite k] [Field κ] [Field Ω]
  [Algebra k κ] [Algebra k Ω] [IsSepClosed κ] [IsSepClosed Ω]

/-- Every actual embedding of the constant closure sends its degree-`n`
constant subfield to the same original degree-`n` subfield of the target. -/
theorem finiteConstantsInClosure_fieldRange (n : ℕ) [NeZero n] (a : κ →ₐ[k] Ω) :
    (a.comp (finiteConstantsInClosure k κ n).toIntermediateField.val).fieldRange =
      (finiteConstantsInClosure k Ω n).toIntermediateField := by
  let A := finiteConstantsInClosure k κ n
  let B := finiteConstantsInClosure k Ω n
  have : Finite A := finite_finiteConstantsInClosure k κ n
  have : Finite B := finite_finiteConstantsInClosure k Ω n
  have hcard : Nat.card A = Nat.card B := by
    rw [Module.natCard_eq_pow_finrank (K := k) (V := A),
      Module.natCard_eq_pow_finrank (K := k) (V := B),
      finrank_finiteConstantsInClosure, finrank_finiteConstantsInClosure]
  have hrange := FieldTheory.finiteFieldEmbedding_range_eq_of_natCard_eq
    (a.comp A.toIntermediateField.val).toRingHom (algebraMap B Ω) hcard
  apply IntermediateField.ext
  intro x
  change x ∈ (a.comp A.toIntermediateField.val).toRingHom.range ↔ x ∈ B.toIntermediateField
  rw [hrange]
  constructor
  · rintro ⟨b, rfl⟩
    exact b.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

end FiniteConstants

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
  [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
  [IsSepClosed Ω]

omit [IsScalarTower k K Ω] in
/-- When the specified finite base is already the original full
constants, the full-constant stage is the actual compositum with the
degree-`n` finite subfield over that same base. -/
theorem fullConstantDegreeStage_eq_adjoin_of_fullConstants
    (hfull : ∀ x : K, IsAlgebraic k x → x ∈ (algebraMap k K).range)
    (n : ℕ) [NeZero n] :
    (fullConstantDegreeStage k K Ω n).toIntermediateField =
      IntermediateField.adjoin K
        ((finiteConstantsInClosure k Ω n).toIntermediateField : Set Ω) := by
  let C := algebraicClosure k K
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite C := FieldTheory.finite_algebraicClosure_of_finite_base k K
  have hsurj : Function.Surjective (Algebra.ofId k C) := by
    intro c
    obtain ⟨a, ha⟩ := hfull (c : K) (mem_algebraicClosure_iff.mp c.property)
    exact ⟨a, Subtype.ext ha⟩
  let b : k ≃ₐ[k] C := AlgEquiv.ofBijective (Algebra.ofId k C)
    ⟨(algebraMap k C).injective, hsurj⟩
  have hcardC : Nat.card C = Nat.card k := (Nat.card_congr b.toEquiv).symm
  let A := finiteConstantsInClosure C Ω n
  let B := finiteConstantsInClosure k Ω n
  have : Finite A := finite_finiteConstantsInClosure C Ω n
  have : Finite B := finite_finiteConstantsInClosure k Ω n
  have hcard : Nat.card A = Nat.card B := by
    rw [Module.natCard_eq_pow_finrank (K := C) (V := A),
      Module.natCard_eq_pow_finrank (K := k) (V := B),
      finrank_finiteConstantsInClosure, finrank_finiteConstantsInClosure, hcardC]
  have hrange := FieldTheory.finiteFieldEmbedding_range_eq_of_natCard_eq
    (algebraMap A Ω) (algebraMap B Ω) hcard
  have hcarrier : (A.toIntermediateField : Set Ω) = (B.toIntermediateField : Set Ω) := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      have hr : x ∈ (algebraMap A Ω).range := ⟨⟨x, hx⟩, rfl⟩
      rw [hrange] at hr
      obtain ⟨b, rfl⟩ := hr
      exact b.property
    · intro hx
      have hr : x ∈ (algebraMap B Ω).range := ⟨⟨x, hx⟩, rfl⟩
      rw [← hrange] at hr
      obtain ⟨a, rfl⟩ := hr
      exact a.property
  change IntermediateField.adjoin K (A.toIntermediateField : Set Ω) =
    IntermediateField.adjoin K (B.toIntermediateField : Set Ω)
  exact congrArg (IntermediateField.adjoin K) hcarrier

end FunctionField
