/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite Galois extensions obtained by adjoining constants

For a finite constant field `C` inside a common overfield, the actual field
`K(C)` is finite Galois over `K`. The constant embedding is the inclusion of
subfields. The Galois assertion follows from the existing theorem that a finite
Galois extension remains Galois after taking a compositum. No condition on the
intersection of `K` with `C` is needed here.
-/

noncomputable section

namespace FunctionField

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (C : IntermediateField k Ω)

/-- The actual constant field embeds into its compositum with `K`. -/
def constantEmbedding : C →ₐ[k] IntermediateField.adjoin K (C : Set Ω) :=
  IntermediateField.inclusion
    (show C ≤ (IntermediateField.adjoin K (C : Set Ω)).restrictScalars k from
      IntermediateField.subset_adjoin K (C : Set Ω))

@[simp]
theorem constantEmbedding_coe (x : C) :
    ((constantEmbedding (K := K) C x : IntermediateField.adjoin K (C : Set Ω)) : Ω) =
      (x : Ω) :=
  rfl

/-- The scalar structure supplied by the actual constant inclusion. -/
abbrev constantAlgebra : Algebra C (IntermediateField.adjoin K (C : Set Ω)) :=
  (constantEmbedding (K := K) C).toRingHom.toAlgebra

/-- The constant inclusion agrees with the original base-field structure. -/
theorem constantScalarTower :
    let _ : Algebra C (IntermediateField.adjoin K (C : Set Ω)) :=
      constantAlgebra (K := K) C
    IsScalarTower k C (IntermediateField.adjoin K (C : Set Ω)) := by
  intro hC
  exact IsScalarTower.of_algebraMap_eq fun x =>
    ((constantEmbedding (K := K) C).commutes x).symm

/-- The images of `C` and `K` generate the actual constant compositum. -/
theorem constantExtension_generatorRanges :
    (constantEmbedding (K := K) C).fieldRange ⊔
      (IsScalarTower.toAlgHom k K (IntermediateField.adjoin K (C : Set Ω))).fieldRange =
      ⊤ := by
  let E := IntermediateField.adjoin K (C : Set Ω)
  let A : IntermediateField k E := (constantEmbedding (K := K) C).fieldRange
  let B : IntermediateField k E := (IsScalarTower.toAlgHom k K E).fieldRange
  let D : IntermediateField k E := A ⊔ B
  let T : Subfield Ω := D.toSubfield.map E.val.toRingHom
  have hC : (C : Set Ω) ⊆ T := by
    intro x hx
    apply Subfield.mem_map.mpr
    refine ⟨constantEmbedding (K := K) C ⟨x, hx⟩, ?_, ?_⟩
    · exact (show A ≤ D from le_sup_left) ⟨⟨x, hx⟩, rfl⟩
    · exact constantEmbedding_coe (K := K) C ⟨x, hx⟩
  have hK : Set.range (algebraMap K Ω) ⊆ T := by
    rintro x ⟨y, rfl⟩
    apply Subfield.mem_map.mpr
    refine ⟨algebraMap K E y, ?_, rfl⟩
    exact (show B ≤ D from le_sup_right) ⟨y, rfl⟩
  have hE : E.toSubfield ≤ T := by
    change (IntermediateField.adjoin K (C : Set Ω)).toSubfield ≤ T
    rw [IntermediateField.adjoin_toSubfield]
    exact Subfield.closure_le.mpr (Set.union_subset hK hC)
  change D = ⊤
  apply top_unique
  intro x _
  exact (Subfield.map_mem_map E.val.toRingHom).mp (hE x.2)

variable [Finite k] [FiniteDimensional k C]

/-- Adjoining finitely many algebraic constants gives a finite extension,
regardless of its intersection with the base function field. -/
theorem finiteDimensional_constantExtension_of_finite :
    FiniteDimensional K (IntermediateField.adjoin K (C : Set Ω)) := by
  have : Finite C := Module.finite_of_finite k
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  have hxk : IsIntegral k x :=
    (Algebra.IsIntegral.isIntegral (R := k) (⟨x, hx⟩ : C)).map C.val
  exact hxk.tower_top

/-- A finite extension of finite constants remains Galois after taking its
actual compositum with the function field. -/
theorem isGalois_constantExtension :
    IsGalois K (IntermediateField.adjoin K (C : Set Ω)) := by
  let E := IntermediateField.adjoin K (C : Set Ω)
  let iC : C →ₐ[k] E := constantEmbedding (K := K) C
  let iK : K →ₐ[k] E := IsScalarTower.toAlgHom k K E
  let A : IntermediateField k E := iC.fieldRange
  let B : IntermediateField k E := iK.fieldRange
  let eA : C ≃ₐ[k] A := iC.equivFieldRange
  let eB : K ≃ₐ[k] B := iK.equivFieldRange
  have : Finite C := Module.finite_of_finite k
  have : FiniteDimensional k A := eA.toLinearEquiv.finiteDimensional
  have : IsGalois k A := IsGalois.of_algEquiv eA
  have : IsGalois B E :=
    IsGalois.sup_right A B (constantExtension_generatorRanges (K := K) C)
  apply IsGalois.of_equiv_equiv (F := B) (E := E) (M := K) (N := E)
    (f := eB.symm.toRingEquiv) (g := RingEquiv.refl E)
  apply RingHom.ext
  intro x
  exact congrArg (fun z : B => (z : E)) (eB.apply_symm_apply x)

/-- The actual constant compositum as a finite Galois intermediate field of the
original ambient extension. -/
def constantExtensionStage : FiniteGaloisIntermediateField K Ω where
  toIntermediateField := IntermediateField.adjoin K (C : Set Ω)
  finiteDimensional := finiteDimensional_constantExtension_of_finite (K := K) C
  isGalois := isGalois_constantExtension (K := K) C

@[simp]
theorem constantExtensionStage_toIntermediateField :
    (constantExtensionStage (K := K) C).toIntermediateField =
      IntermediateField.adjoin K (C : Set Ω) :=
  rfl

end FunctionField
