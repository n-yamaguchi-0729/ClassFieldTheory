/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.AlgebraicPointFiniteField
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower

/-!
# Every algebraic point over a finite field is Frobenius-periodic

The finite field of definition of the specified point supplies a positive
period. The assertion concerns the original scheme morphism, not a replacement point.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Each actual algebraic point of a separated finite-type scheme has positive Frobenius period. -/
theorem exists_frobenius_period_of_algebraic_point
    (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsSeparated f]
    (p : Spec (CommRingCat.of Ω) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ n : ℕ, n ≠ 0 ∧
      Spec.map (CommRingCat.ofHom
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ n).toRingHom) ≫ p = p := by
  obtain ⟨E, hE, q, -, hq⟩ :=
    exists_finite_intermediateField_point_factorization k Ω f p hp
  have : Module.Finite k E := hE
  have : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := k) E
  refine ⟨Module.finrank k E, (Module.finrank_pos (R := k) (M := E)).ne', ?_⟩
  rw [← hq, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change ((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ Module.finrank k E)
    (algebraMap E Ω a) = algebraMap E Ω a
  rw [← FiniteField.frobeniusAlgEquiv_restrictScalars k E Ω]
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic E Ω).commutes a

end AlgebraicGeometry
