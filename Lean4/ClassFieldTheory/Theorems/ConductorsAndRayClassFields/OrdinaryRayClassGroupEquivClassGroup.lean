import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.OrdinaryClassGroupComparison
import Mathlib.RingTheory.ClassGroup.Basic

set_option autoImplicit false

/-!
# The ordinary ray class group is the ideal class group

At the modulus with no finite or real conditions, the ideal-theoretic ray
class group agrees with Mathlib's ideal class group. The comparison also
preserves the class of each finite prime, fixing its arithmetic meaning.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- The ordinary ray class group is isomorphic to the ideal class group,
and the isomorphism sends each finite-prime ray class to its ideal class. -/
theorem exists_ordinaryRayClassGroupEquivClassGroup
    (K : Type) [Field K] [NumberField K] :
    ∃ e : RayClassGroup (ordinaryRayClassModulus K) ≃* ClassGroup (𝓞 K),
      ∀ v : HeightOneSpectrum (𝓞 K),
        e (ordinaryRayClassOfFinitePrime v) =
          ClassGroup.mk K (finitePrimeFractionalIdeal v) := by
  refine ⟨ordinaryRayClassGroupEquivClassGroup (K := K), ?_⟩
  intro v
  exact ordinaryRayClassGroupEquivClassGroup_prime (K := K) v

end ClassFieldTheory
