/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.ArtinSchreierSplit
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SupportedLocalNorms
import Nyll.GaloisCohomology.ArtinSchreier.FiniteExtension

/-!
# Detecting supported Artin–Schreier classes locally

For a finite set representing all idele classes, an integral parameter away
from that set has trivial global Artin–Schreier class if its local classes
there are trivial. The proof constructs the actual cyclic root extension,
establishes its local norms, and forces its degree to be one.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- Supported local roots detect the actual global Artin–Schreier class. -/
theorem exists_artinSchreier_root_of_supported_local_roots
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset (Place k K)) (hS : Function.Surjective (IdeleGroup.sIdeleClass S))
    (a : K)
    (hAway : ∀ v : Place k K, v ∉ S → a ∈ v.toValuationSubring)
    (hLocal : ∀ v : Place k K, v ∈ S → ∃ x : v.adicCompletion,
      x ^ p - x = algebraMap K v.adicCompletion a) :
    ∃ x : K, x ^ p - x = a := by
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨E, hcyclic, β, hβ, hgen⟩ :=
    ArtinSchreierTheory.exists_finite_cyclic_extension p K Ω a
  have hEcyclic : IsCyclic Gal(E/K) := hcyclic
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K E
  let aRE : Algebra (RatFunc k) E := presentation.val
  have hkRE : IsScalarTower k (RatFunc k) E := presentation.property.1
  have hEfunction : FunctionField k E := presentation.property.2
  have hEcurve : IsCurveOver k E := isCurveOver k E
  have hUnramified (w : Place k E) (hw : w.restrict K ∉ S) :
      w.ramificationIndex K = 1 :=
    artinSchreier_ramificationIndex_eq_one p a β hβ hgen w (hAway (w.restrict K) hw)
  have hSplit (v : Place k K) (hv : v ∈ S) (w : Place k E) (hw : w.restrict K = v) :
      Function.Surjective (IdeleGroup.localNormOver v w hw) := by
    subst v
    obtain ⟨x, hx⟩ := hLocal (w.restrict K) hv
    exact IdeleGroup.localNorm_surjective_of_artinSchreier_root p w a β hβ hgen x hx
  have hdegree : Module.finrank K E = 1 :=
    finrank_eq_one_of_supported_local_norms S hS hUnramified hSplit
  obtain ⟨x, hx⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegree).2 β
  refine ⟨x, (algebraMap K E).injective ?_⟩
  rw [map_sub, map_pow, hx, hβ]

/-- The finite detecting set is supplied by the actual Picard group. -/
theorem exists_finset_artinSchreier_detection
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ S : Finset (Place k K), ∀ a : K,
      (∀ v : Place k K, v ∉ S → a ∈ v.toValuationSubring) →
      (∀ v : Place k K, v ∈ S → ∃ x : v.adicCompletion,
        x ^ p - x = algebraMap K v.adicCompletion a) →
      ∃ x : K, x ^ p - x = a := by
  obtain ⟨S, hS⟩ := IdeleGroup.exists_finset_sIdeleClass_surjective k K
  exact ⟨S, fun a ha hlocal =>
    exists_artinSchreier_root_of_supported_local_roots p S hS a ha hlocal⟩

end FunctionField
