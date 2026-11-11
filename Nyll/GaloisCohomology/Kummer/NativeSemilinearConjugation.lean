/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearClosureTransport
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Original semilinear conjugation on a native absolute Galois group

An actual automorphism of a supplied separable closure is transported along
the actual native closure equivalence. Its conjugation is continuous for
the original Krull topology. After the original topological abelianization,
the action depends only on the original base-field automorphism, including
when the ambient lift or the closure comparison is changed.
-/

@[expose] public section

noncomputable section

namespace KummerTheory

open ProCGroups.Abelian

universe u v

variable {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω]
  (e : SeparableClosure F ≃ₐ[F] Ω) (τ : F ≃+* F) (a : Ω ≃+* Ω)
  (ha : ∀ x : F, a (algebraMap F Ω x) = algebraMap F Ω (τ x))

/-- The actual ambient semilinear automorphism transported to the native
separable closure, with no change of the original field coefficients. -/
def nativeSemilinearClosureEquiv : SeparableClosure F ≃+* SeparableClosure F :=
  transportSemilinearEquiv e.symm a

include ha in
/-- The transported native automorphism induces exactly the same
original base-field automorphism. -/
theorem nativeSemilinearClosureEquiv_algebraMap (x : F) :
    nativeSemilinearClosureEquiv e a (algebraMap F (SeparableClosure F) x) =
      algebraMap F (SeparableClosure F) (τ x) :=
  transportSemilinearEquiv_algebraMap τ e.symm a ha x

/-- Original continuous Galois conjugation by the actual native lift. -/
def nativeSemilinearGaloisEquiv :
    Gal(SeparableClosure F/F) ≃ₜ* Gal(SeparableClosure F/F) :=
  semilinearGaloisConjugateContinuousEquiv τ (nativeSemilinearClosureEquiv e a)
    (nativeSemilinearClosureEquiv_algebraMap e τ a ha)

/-- The native action is literal semilinear conjugation in the original
supplied closure after its actual comparison. -/
theorem nativeSemilinearGaloisEquiv_ambient (σ : Gal(SeparableClosure F/F)) :
    AlgEquiv.autCongr e (nativeSemilinearGaloisEquiv e τ a ha σ) =
      semilinearGaloisConjugate τ a ha (AlgEquiv.autCongr e σ) := by
  apply AlgEquiv.ext
  intro x
  change e (e.symm (a (e (σ (e.symm (a.symm (e (e.symm x)))))))) =
    a (e (σ (e.symm (a.symm x))))
  rw [e.apply_symm_apply, e.apply_symm_apply]

/-- The same original action on the full native absolute abelianization. -/
def nativeSemilinearAbsoluteAbelianEquiv :
    TopologicalAbelianization Gal(SeparableClosure F/F) ≃ₜ*
      TopologicalAbelianization Gal(SeparableClosure F/F) :=
  TopologicalAbelianization.congr (nativeSemilinearGaloisEquiv e τ a ha)

/-- Original native Galois representatives are retained under the
semilinear abelian action. -/
theorem nativeSemilinearAbsoluteAbelianEquiv_mk (σ : Gal(SeparableClosure F/F)) :
    nativeSemilinearAbsoluteAbelianEquiv e τ a ha
        (TopologicalAbelianization.mk Gal(SeparableClosure F/F) σ) =
      TopologicalAbelianization.mk Gal(SeparableClosure F/F)
        (nativeSemilinearGaloisEquiv e τ a ha σ) := rfl

/-- Changing the supplied closure comparison or the ambient lift of the
same original field automorphism leaves the full native abelian action
unchanged. The discrepancy is an actual inner Galois conjugation. -/
theorem nativeSemilinearAbsoluteAbelianEquiv_eq
    (e' : SeparableClosure F ≃ₐ[F] Ω) (a' : Ω ≃+* Ω)
    (ha' : ∀ x : F, a' (algebraMap F Ω x) = algebraMap F Ω (τ x)) :
    nativeSemilinearAbsoluteAbelianEquiv e τ a ha =
      nativeSemilinearAbsoluteAbelianEquiv e' τ a' ha' := by
  apply ContinuousMulEquiv.ext
  intro z
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure F/F) z
  exact (map_semilinearGaloisConjugate_eq
    (TopologicalAbelianization.mk Gal(SeparableClosure F/F)) τ
    (nativeSemilinearClosureEquiv e a) (nativeSemilinearClosureEquiv e' a')
    (nativeSemilinearClosureEquiv_algebraMap e τ a ha)
    (nativeSemilinearClosureEquiv_algebraMap e' τ a' ha') σ).symm

end KummerTheory
