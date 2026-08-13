import LocalFieldTheory.NonarchimedeanLocalField.PowerClassFiniteness
import KummerTheory.Concrete.MaximalKummerSubgroup
import KummerTheory.Concrete.KummerCorrespondenceFormula

/-!
# Maximal finite Kummer extensions of local fields

For a positive integer `n` that is nonzero in a nonarchimedean local field,
the Kummer extension obtained by adjoining all `n`-th roots is finite.
-/

noncomputable section

universe v

namespace KummerTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The maximal restricted radical quotient is finite when the exponent is
nonzero in the local field. -/
theorem finite_maximalRestrictedRadicalQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) :
    Finite (RestrictedRadicalQuotient n (maximalKummerSubgroup K n)) := by
  letI : Finite (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero
      K (n : ℕ) hnK
  exact Finite.of_equiv
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
    (maximalRestrictedRadicalQuotientEquiv K n).toEquiv

variable {Omega : Type v} [Field Omega] [Algebra K Omega] [IsSepClosure K Omega]

/-- The maximal exponent-`n` Kummer extension is finite-dimensional. -/
theorem maximalKummerRadicalExtension_finiteDimensional
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    FiniteDimensional K
      (kummerRadicalExtension (K := K) (Omega := Omega) n
        (maximalKummerSubgroup K n).1) := by
  let Delta := maximalKummerSubgroup K n
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1
  let R := RestrictedRadicalQuotient n Delta
  let M := nthRootsSubgroup E (n : ℕ)
  letI : IsGalois K E :=
    kummerRadicalExtension_isGalois (K := K) (Omega := Omega) n Delta.1
  letI : Finite R := finite_maximalRestrictedRadicalQuotient K n hnK
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  letI : Fintype M := nthRootsSubgroupFintype E (n : ℕ)
  letI : Finite (R →* M) :=
    Finite.of_injective (fun chi : R →* M => (chi : R → M))
      DFunLike.coe_injective
  let e := kummerRadicalExtensionRestrictedTransposeMulEquiv
    (K := K) (Omega := Omega) n hnK hmu Delta
  letI : Finite Gal(E/K) := Finite.of_equiv (R →* M) e.symm.toEquiv
  exact IsGalois.finiteDimensional_of_finite K E

end KummerTheory

end
