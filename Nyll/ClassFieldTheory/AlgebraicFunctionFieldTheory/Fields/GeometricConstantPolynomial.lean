/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantTower
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Descending polynomial data from the geometric constant extension

Finitely many polynomials, including minimal polynomials and the numerator and
denominator of a rational expression, are defined over one finite constant stage.
-/

noncomputable section

namespace FunctionField

open Polynomial

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- A finite family of geometric polynomials has a common actual finite constant field
of definition, with its given embedding into the geometric field. -/
theorem exists_fullConstantDegreeStage_polynomial_lifts
    (P : Finset (Polynomial (geometricConstantExtension k K Ω))) :
    ∃ n : ℕ+, ∃ h : (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField ≤
        geometricConstantExtension k K Ω,
      ∀ p ∈ P, p ∈ Polynomial.lifts (IntermediateField.inclusion h).toRingHom := by
  classical
  let A := geometricConstantExtension k K Ω
  let S : Finset Ω := P.biUnion (fun p => p.coeffs.image (fun a : A => (a : Ω)))
  have hS : ∀ x ∈ S, x ∈ A := by
    intro x hx
    obtain ⟨p, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact a.property
  obtain ⟨n, hn⟩ := exists_fullConstantDegreeStage_containing_finset k K Ω S hS
  have h : (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField ≤ A := by
    change (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField ≤
      geometricConstantExtension k K Ω
    rw [geometricConstantExtension_eq_iSup]
    exact le_iSup (fun m : ℕ+ =>
      (fullConstantDegreeStage k K Ω (m : ℕ)).toIntermediateField) n
  refine ⟨n, h, fun p hp => (Polynomial.lifts_iff_coeffs_subset_range p).mpr ?_⟩
  intro a ha
  have hamem := hn (a : Ω) (Finset.mem_biUnion.mpr
    ⟨p, hp, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)
  exact ⟨⟨(a : Ω), hamem⟩, Subtype.ext rfl⟩

/-- A simple geometric extension and a specified element descend to a stage at which
the minimal polynomial, and hence the extension degree, is already unchanged. -/
theorem exists_fullConstantDegreeStage_minpoly_and_mem_adjoin
    (α x : Ω) (hα : IsIntegral K α)
    (hx : x ∈ IntermediateField.adjoin (geometricConstantExtension k K Ω) {α}) :
    ∃ n : ℕ+, ∃ h : (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField ≤
        geometricConstantExtension k K Ω,
      (minpoly (fullConstantDegreeStage k K Ω (n : ℕ)) α).map
          (IntermediateField.inclusion h).toRingHom =
        minpoly (geometricConstantExtension k K Ω) α ∧
      x ∈ IntermediateField.adjoin (fullConstantDegreeStage k K Ω (n : ℕ)) {α} := by
  classical
  let A := geometricConstantExtension k K Ω
  obtain ⟨r, s, hxs⟩ := (IntermediateField.mem_adjoin_simple_iff (F := A) x).mp hx
  obtain ⟨n, h, hlift⟩ := exists_fullConstantDegreeStage_polynomial_lifts k K Ω
    {minpoly A α, r, s}
  let B := (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField
  let : Algebra B A := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower B A Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmin : (minpoly A α) ∈ Polynomial.lifts (algebraMap B A) :=
    hlift _ (Finset.mem_insert_self _ _)
  have hr : r ∈ Polynomial.lifts (algebraMap B A) :=
    hlift _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hs : s ∈ Polynomial.lifts (algebraMap B A) :=
    hlift _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  refine ⟨n, h, minpoly.map_algebraMap (hα.tower_top (A := B)) hmin, ?_⟩
  obtain ⟨r', hr'⟩ := (Polynomial.mem_lifts r).mp hr
  obtain ⟨s', hs'⟩ := (Polynomial.mem_lifts s).mp hs
  apply (IntermediateField.mem_adjoin_simple_iff (F := B) x).mpr
  refine ⟨r', s', ?_⟩
  rw [← hr', ← hs', Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap] at hxs
  exact hxs

end FunctionField
