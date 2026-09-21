import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius

set_option autoImplicit false

/-!
# Arithmetic Frobenius at a finite prime
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Mathlib's chosen arithmetic Frobenius lift at a finite prime of the
extension field.  At a ramified prime such a lift need not be unique. -/
def arithmeticFrobeniusAt
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (w : HeightOneSpectrum (𝓞 L)) : L ≃ₐ[K] L :=
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal

end ClassFieldTheory
