/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_two_mul_genusFF_sub_one_ge_of_isSplittingField_X_pow_sub_C.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.IsAlgebraicAdjoinTranscendental
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite extensions of simple intermediate fields
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FiniteDimensional_adjoin_of_transcendental

open Set Cardinal

namespace AlgebraicCurve
namespace FF2KE3

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finiteDimensional_adjoin_of_transcendental' (x : F)
    [hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    _root_.AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x ht
  set E := IntermediateField.adjoin K ({t} : Set F)
  set Kx := IntermediateField.adjoin K ({x} : Set F)
  let b := Module.finBasis Kx F
  let S : Set F := insert x (Set.range b)
  have : Finite S := Set.Finite.insert x (Set.finite_range b) |>.to_subtype
  have hM : FiniteDimensional E (IntermediateField.adjoin E S) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (halg.isAlgebraic y).isIntegral
  have htop : IntermediateField.adjoin E S = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hKx : ∀ c : Kx, (c : F) ∈ IntermediateField.adjoin E S := by
      intro c
      have hle : Kx ≤ (IntermediateField.adjoin E S).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.subset_adjoin E S (Set.mem_insert _ _)
      exact hle c.2
    rw [← b.sum_repr y]
    refine Subfield.sum_mem _ fun i _ => ?_
    rw [IntermediateField.smul_def]
    exact mul_mem (hKx _) (IntermediateField.subset_adjoin E S (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  rw [htop] at hM
  exact (IntermediateField.topEquiv (F := E) (E := F)).toLinearEquiv.finiteDimensional

end AlgebraicCurve.FF2KE3

theorem _root_.AlgebraicCurve.finiteDimensional_adjoin_of_transcendental {K F : Type*} [Field K]
  [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental
      K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.FF2KE3.finiteDimensional_adjoin_of_transcendental' x ht
end AlgebraicCurves.FunctionFields.Proofs.FiniteDimensional_adjoin_of_transcendental
end ProofImplementation

namespace AlgebraicCurve

open IntermediateField

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
  {F' : Type*} [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']

/-- A finite extension of a field finite over a simple intermediate field remains finite
relative to the image of that intermediate field. -/
theorem finiteDimensional_adjoin_algebraMap (x : F) (hfin : FiniteDimensional L⟮x⟯ F)
    [FiniteDimensional F F'] :
    FiniteDimensional L⟮algebraMap F F' x⟯ F' := by
  have := hfin
  let φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F'
  have : Module.Finite L⟮x⟯ F' := Module.Finite.trans F F'
  have hmap : L⟮x⟯.map φ = L⟮algebraMap F F' x⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : L⟮x⟯ ≃ₐ[L] L⟮algebraMap F F' x⟯ :=
    (L⟮x⟯.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  refine Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F') ?_
  ext y
  rfl

end AlgebraicCurve
