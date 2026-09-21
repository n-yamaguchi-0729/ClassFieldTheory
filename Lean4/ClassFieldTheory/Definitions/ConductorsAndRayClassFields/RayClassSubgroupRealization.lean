import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension

set_option autoImplicit false

/-!
# Class fields attached to ray class subgroups
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A finite abelian class field realizing a subgroup of a ray class group.

The Artin map has exactly the prescribed kernel and is normalized on prime
classes by arithmetic Frobenius. -/
structure RayClassSubgroupRealization
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) where
  /-- The corresponding finite abelian extension. -/
  extension : FiniteAbelianExtension K
  /-- The extension is unramified away from the modulus. -/
  unramifiedOutsideModulus :
    IsUnramifiedOutsideModulus K extension m
  /-- The Artin map attached to the extension. -/
  artin : RayClassGroup m →* (extension ≃ₐ[K] extension)
  /-- The Artin map is onto. -/
  artin_surjective : Function.Surjective artin
  /-- The prescribed subgroup is exactly the Artin kernel. -/
  artin_ker : artin.ker = H
  /-- A prime class maps to arithmetic Frobenius. -/
  artin_frobenius :
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support)
      (w : HeightOneSpectrum (𝓞 extension)),
      w.asIdeal.LiesOver v.asIdeal →
        artin (rayClassOfFinitePrime m v hv) =
          arithmeticFrobeniusAt (K := K) w

end ClassFieldTheory
