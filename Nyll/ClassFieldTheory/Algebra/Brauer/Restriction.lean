/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Nyll.ClassFieldTheory.Algebra.Brauer.Cohomology
public import Nyll.GaloisCohomology.Topology.SeparableGaloisMap

/-!
# Restriction of cohomological Brauer classes

The restriction uses the actual Galois pullback and the induced map on units
from the same embedding of separable closures.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped ContRepresentation

namespace ClassFieldTheory.Brauer

section Coefficients

variable {K : Type v} {L : Type w} {E F : Type u}
    [Field K] [Field L] [Field E] [Field F] [Algebra K E] [Algebra L F]

/-- The intertwining map of units induced by an equivariant embedding of extensions. -/
def galoisUnitsMap (r : Gal(F/L) →ₜ* Gal(E/K)) (f : E →+* F)
    (commutes : ∀ (g : Gal(F/L)) (x : E), f (r g x) = g (f x)) :
    TopRep.res r.toMonoidHom (galoisUnitsRep K E) ⟶ galoisUnitsRep L F := by
  let X := TopRep.res r.toMonoidHom (galoisUnitsRep K E)
  let Y := galoisUnitsRep L F
  let m : X →ₗ[ℤ] Y := (Units.map f.toMonoidHom).toAdditive.toIntLinearMap
  let : DiscreteTopology X := galoisUnitsRep_discrete K E
  let φ : X.ρ →ⁱL Y.ρ := {
    toLinearMap := m
    cont := continuous_of_discreteTopology
    isIntertwining' := fun g => by
      apply ContinuousLinearMap.ext
      intro a
      apply Units.ext
      exact commutes g ((show Additive Eˣ from a).toMul : E) }
  exact ConcreteCategory.ofHom φ

/-- The underlying map of coefficients is the original map of units. -/
theorem galoisUnitsMap_apply (r : Gal(F/L) →ₜ* Gal(E/K)) (f : E →+* F)
    (commutes : ∀ (g : Gal(F/L)) (x : E), f (r g x) = g (f x)) (a : Additive Eˣ) :
    galoisUnitsMap r f commutes a = Additive.ofMul (Units.map f.toMonoidHom a.toMul) :=
  rfl

/-- The actual cohomology map obtained from an equivariant homomorphism of field units. -/
def transportCohomology (n : ℕ)
    (r : Gal(F/L) →ₜ* Gal(E/K)) (f : E →+* F)
    (h : ∀ (σ : Gal(F/L)) (x : E), f (r σ x) = σ (f x)) :
    continuousCohomology n (galoisUnitsRep K E) →+
      continuousCohomology n (galoisUnitsRep L F) :=
  (ContinuousCohomology.map r (galoisUnitsMap r f h) n).hom.toLinearMap.toAddMonoidHom

end Coefficients

variable {K L : Type u} [Field K] [Field L]

/-- The restriction on degree-two classes for a fixed embedding and its Galois map. -/
def restrictOfEmbedding
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (f : SeparableClosure K →+* SeparableClosure L)
    (commutes : ∀ (g : Gal(SeparableClosure L/L)) (x : SeparableClosure K),
      f (r g x) = g (f x)) : Br K →+ Br L :=
  transportCohomology 2 r f commutes

/-- Restrict using the separable-closure map extending the specified field embedding. -/
def restrict (f : K →+* L) : Br K →+ Br L :=
  restrictOfEmbedding (Field.absoluteGaloisGroup.separableMap f)
    (Field.absoluteGaloisGroup.separableClosureLift f)
    (Field.absoluteGaloisGroup.separableMap_commutes f)

/-- On a cocycle the embedding-based restriction is the standard restriction of cochains. -/
theorem restrictOfEmbedding_π
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (f : SeparableClosure K →+* SeparableClosure L)
    (commutes : ∀ (g : Gal(SeparableClosure L/L)) (x : SeparableClosure K),
      f (r g x) = g (f x))
    (z : ContinuousCohomology.cocycles (unitsRep K) 2) :
    restrictOfEmbedding r f commutes (ContinuousCohomology.π (unitsRep K) 2 z) =
      ContinuousCohomology.π (unitsRep L) 2
        (ContinuousCohomology.cocyclesMap r (galoisUnitsMap r f commutes) 2 z) :=
  ConcreteCategory.congr_hom (ContinuousCohomology.π_map r (galoisUnitsMap r f commutes) 2) z

end ClassFieldTheory.Brauer
