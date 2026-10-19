/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Approximation
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion
import Nyll.GaloisCohomology.ArtinSchreier.FieldMapApproximation
import Nyll.ValuedFieldTheory.Valuation.Henselian.ArtinSchreier
import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete

/-!
# Simultaneous Artin–Schreier approximation at actual function-field places

For any finite family of distinct places, one global field element realizes
arbitrary Artin–Schreier classes in all the actual completions. Consequently
every finite family of local prime cyclic Galois characters is the restriction
of a single global character. Local openness is proved from the actual complete
discrete valuation rings, and approximation is supplied by the proved diagonal
density of the function field.

No behavior at places outside the prescribed finite family is asserted.
-/

open scoped WithZero
noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

local instance artinSchreierCompletionCharP (v : AlgebraicCurve.Place k K)
    (p : ℕ) [CharP K p] : CharP v.adicCompletion p :=
  charP_of_injective_algebraMap (algebraMap K v.adicCompletion).injective p

/-- One global element realizes any prescribed finite family of local
Artin–Schreier classes at distinct actual places. -/
theorem surjective_pi_placeCompletion_artinSchreierClasses
    {ι : Type*} [Finite ι] (v : ι → AlgebraicCurve.Place k K)
    (hv : Function.Injective v) (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Surjective (fun (a : K) (i : ι) =>
      (algebraMap K (v i).adicCompletion a :
        (v i).adicCompletion ⧸
          ((frobenius (v i).adicCompletion p).toAddMonoidHom -
            AddMonoidHom.id (v i).adicCompletion).range)) := by
  classical
  intro c
  let N (i : ι) : AddSubgroup (v i).adicCompletion :=
    ((frobenius (v i).adicCompletion p).toAddMonoidHom -
      AddMonoidHom.id (v i).adicCompletion).range
  obtain ⟨a, ha⟩ := Classical.axiomOfChoice
    (fun i => QuotientAddGroup.mk'_surjective (N i) (c i))
  let U (i : ι) : Set (v i).adicCompletion := {x | -(a i) + x ∈ N i}
  have hN (i : ι) : IsOpen (N i : Set (v i).adicCompletion) := by
    have : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
        (Valued.v : Valuation (v i).adicCompletion ℤᵐ⁰) :=
      (ValuationTheory.Valuations.completeDVFOfCompleteValuedField
        (K := (v i).adicCompletion) (Gamma := ℤᵐ⁰)).instCompleteDiscrete
    have := ValuationTheory.DiscreteValuationField.Valuation.henselianRing
      (Valued.v : Valuation (v i).adicCompletion ℤᵐ⁰)
    exact ValuationTheory.isOpen_artinSchreier_range (Γ := ℤᵐ⁰) p
  have hU (i : ι) : IsOpen (U i) :=
    (hN i).preimage (continuous_const.add continuous_id)
  have haU (i : ι) : a i ∈ U i := by
    change -(a i) + a i ∈ N i
    rw [neg_add_cancel]
    exact (N i).zero_mem
  obtain ⟨x, hx⟩ := (denseRange_pi_placeCompletion v hv).exists_mem_open
    (isOpen_set_pi Set.finite_univ (fun i _ => hU i))
    (show (Set.univ.pi U).Nonempty from ⟨a, fun i _ => haU i⟩)
  refine ⟨x, funext (fun i => ?_)⟩
  exact (QuotientAddGroup.eq.mpr (hx i (Set.mem_univ i))).symm.trans (ha i)

/-- Any finite family of local prime cyclic characters at distinct actual
places is the restriction of one global prime cyclic character. -/
theorem surjective_pi_placeCompletion_artinSchreierCharacters
    {ι : Type*} [Finite ι] (v : ι → AlgebraicCurve.Place k K)
    (hv : Function.Injective v) (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Surjective
      (fun χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p) =>
        fun i => χ.comp
          (Field.absoluteGaloisGroup.map (algebraMap K (v i).adicCompletion))) :=
  ClassFieldTower.Martinet.Shafarevich.surjective_characters_of_artinSchreierClasses
    (fun i => (v i).adicCompletion) p (fun i => algebraMap K (v i).adicCompletion)
    (surjective_pi_placeCompletion_artinSchreierClasses v hv p)

end FunctionField
