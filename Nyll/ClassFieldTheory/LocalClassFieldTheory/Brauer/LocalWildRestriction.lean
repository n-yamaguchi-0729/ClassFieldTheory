/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteInflation
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianAlgebraicRamificationRestriction

/-! # Finite-stage restriction of absolute wild inertia -/

@[expose] public section

noncomputable section

open RamificationTheory.HilbertRamification.ValuationSubring

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K]

/-- Restriction of the original absolute Galois group maps the actual wild
subgroup onto the wild subgroup for the restricted finite-stage valuation. -/
theorem localWild_finiteGaloisRestriction_map (V : ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (W : ValuationSubring (SeparableClosure K)) [V.valuation.HasExtension W.valuation]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField W) p] :
    (ramificationGroupInAut K W).map (finiteGaloisRestriction E).toMonoidHom =
      ramificationGroupInAut K (W.comap E.toIntermediateField.val.toRingHom) := by
  let j := E.toIntermediateField.val.toRingHom
  let W₀ := W.comap j
  have hj : j.comp (algebraMap K E) = (algebraMap K (SeparableClosure K)).comp (RingHom.id K) :=
    RingHom.ext E.toIntermediateField.val.commutes
  let f : ramificationGroup K W →* ramificationGroup K W₀ :=
    _root_.HilbertRamification.ValuationSubring.galoisPullback_ramificationGroupMap
      (RingHom.id K) j hj W
  have hf : Function.Surjective f :=
    galoisPullback_ramificationGroupMap_surjective_of_isGalois_henselianRing V W E p
  have hcomm (σ : ramificationGroup K W) :
      inertiaGroupToAut (K := K) W₀ (f σ).val =
        finiteGaloisRestriction E (inertiaGroupToAut (K := K) W σ.val) := by
    apply AlgEquiv.ext
    intro a
    apply j.injective
    exact (_root_.HilbertRamification.galoisPullback_galoisPullback_commutes
      (RingHom.id K) j hj (inertiaGroupToAut (K := K) W σ.val) a).trans
      (finiteGaloisRestriction_commutes E (inertiaGroupToAut (K := K) W σ.val) a).symm
  ext g
  constructor
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    let t := f ⟨σ, hσ⟩
    exact ⟨t.val, t.property, hcomm ⟨σ, hσ⟩⟩
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨σ, hσ⟩ := hf ⟨τ, hτ⟩
    refine ⟨_, ⟨σ.val, σ.property, rfl⟩, ?_⟩
    exact (hcomm σ).symm.trans (congrArg (fun t : ramificationGroup K W₀ =>
      inertiaGroupToAut (K := K) W₀ t.val) hσ)

end ClassFieldTheory.Brauer
