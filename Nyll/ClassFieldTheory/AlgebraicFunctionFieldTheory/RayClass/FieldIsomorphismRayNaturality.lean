/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.DegreeOneAbsoluteGalois
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.DegreeOneRayNaturality
public import Nyll.GaloisCohomology.Kummer.NativeSemilinearConjugation

/-!
# Actual native reciprocity for a specified field isomorphism

A field isomorphism supplies its literal degree-one coefficient algebra.
The specified compatible isomorphism of native separable closures supplies
the original Galois conjugation, including its Krull topology. When the
field isomorphism fixes the stated finite constants, degree-one reciprocity
gives the native ray square on the actual restricted product.

The general native Galois comparison also accepts arbitrary field ring
isomorphisms. Its specialization to a semilinear automorphism is exactly
the existing native semilinear conjugation, not a replacement action.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve LocalClassFieldTheory ProCGroups.Abelian

namespace FunctionField

section NativeFields

variable {K : Type u} {F : Type v} [Field K] [Field F]

/-- The original field isomorphism, linear over its own literal coefficient
map. The source uses its original identity scalar structure. -/
def fieldIsoAsAlgEquiv (τ : K ≃+* F) :
    let : Algebra K F := τ.toRingHom.toAlgebra
    K ≃ₐ[K] F := by
  intro fieldAlgebra
  exact { τ with commutes' := fun _ => rfl }

/-- The inverse closure comparison is linear for precisely the coefficient
map determined by the specified original field isomorphism. -/
def fieldIsoClosureBackEquiv
    (τ : K ≃+* F) (a : SeparableClosure K ≃+* SeparableClosure F)
    (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
      algebraMap F (SeparableClosure F) (τ x)) :
    let : Algebra K (SeparableClosure F) :=
      ((algebraMap F (SeparableClosure F)).comp τ.toRingHom).toAlgebra
    SeparableClosure F ≃ₐ[K] SeparableClosure K := by
  intro closureAlgebra
  exact { a.symm with
    commutes' := fun x => by
      change a.symm (algebraMap F (SeparableClosure F) (τ x)) =
        algebraMap K (SeparableClosure K) x
      rw [← ha, a.symm_apply_apply] }

/-- Native Galois conjugation by the specified original field and closure
isomorphisms, with continuity obtained from the original degree-one
restriction comparison. -/
def nativeFieldIsoGaloisEquiv
    (τ : K ≃+* F) (a : SeparableClosure K ≃+* SeparableClosure F)
    (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
      algebraMap F (SeparableClosure F) (τ x)) :
    Gal(SeparableClosure K/K) ≃ₜ* Gal(SeparableClosure F/F) := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  let : Algebra K (SeparableClosure F) :=
    ((algebraMap F (SeparableClosure F)).comp τ.toRingHom).toAlgebra
  have : IsScalarTower K F (SeparableClosure F) := IsScalarTower.of_algebraMap_eq' rfl
  let e := fieldIsoAsAlgEquiv τ
  have hdegree : Module.finrank K F = 1 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  exact (degreeOneAbsoluteGaloisEquiv K F hdegree (fieldIsoClosureBackEquiv τ a ha)).symm

/-- The native comparison acts by the literal specified closure conjugation. -/
theorem nativeFieldIsoGaloisEquiv_apply
    (τ : K ≃+* F) (a : SeparableClosure K ≃+* SeparableClosure F)
    (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
      algebraMap F (SeparableClosure F) (τ x))
    (σ : Gal(SeparableClosure K/K)) (x : SeparableClosure F) :
    nativeFieldIsoGaloisEquiv τ a ha σ x = a (σ (a.symm x)) := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  let : Algebra K (SeparableClosure F) :=
    ((algebraMap F (SeparableClosure F)).comp τ.toRingHom).toAlgebra
  have : IsScalarTower K F (SeparableClosure F) := IsScalarTower.of_algebraMap_eq' rfl
  let e := fieldIsoAsAlgEquiv τ
  have hdegree : Module.finrank K F = 1 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  exact degreeOneAbsoluteGaloisEquiv_symm_apply
    K F hdegree (fieldIsoClosureBackEquiv τ a ha) σ x

/-- The same original closure conjugation on native absolute abelianizations. -/
def nativeFieldIsoAbelianEquiv
    (τ : K ≃+* F) (a : SeparableClosure K ≃+* SeparableClosure F)
    (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
      algebraMap F (SeparableClosure F) (τ x)) :
    localAbsoluteAbelianProfinite K ≃ₜ* localAbsoluteAbelianProfinite F :=
  TopologicalAbelianization.congr (nativeFieldIsoGaloisEquiv τ a ha)

/-- Native Galois representatives retain their original closure action. -/
theorem nativeFieldIsoAbelianEquiv_mk
    (τ : K ≃+* F) (a : SeparableClosure K ≃+* SeparableClosure F)
    (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
      algebraMap F (SeparableClosure F) (τ x)) (σ : Gal(SeparableClosure K/K)) :
    nativeFieldIsoAbelianEquiv τ a ha
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
      (QuotientGroup.mk (nativeFieldIsoGaloisEquiv τ a ha σ) :
        localAbsoluteAbelianProfinite F) := rfl

/-- At an actual semilinear automorphism this is precisely the original
native action transported from the specified ambient closure. -/
theorem nativeFieldIsoAbelianEquiv_eq_nativeSemilinear
    {Ω : Type w} [Field Ω] [Algebra K Ω]
    (e : SeparableClosure K ≃ₐ[K] Ω) (τ : K ≃+* K) (a : Ω ≃+* Ω)
    (ha : ∀ x : K, a (algebraMap K Ω x) = algebraMap K Ω (τ x)) :
    nativeFieldIsoAbelianEquiv τ (KummerTheory.nativeSemilinearClosureEquiv e a)
        (KummerTheory.nativeSemilinearClosureEquiv_algebraMap e τ a ha) =
      KummerTheory.nativeSemilinearAbsoluteAbelianEquiv e τ a ha := by
  have hGalois :
      nativeFieldIsoGaloisEquiv τ (KummerTheory.nativeSemilinearClosureEquiv e a)
          (KummerTheory.nativeSemilinearClosureEquiv_algebraMap e τ a ha) =
        KummerTheory.nativeSemilinearGaloisEquiv e τ a ha := by
    apply ContinuousMulEquiv.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    rw [nativeFieldIsoGaloisEquiv_apply]
    rfl
  exact congrArg
    (fun φ : Gal(SeparableClosure K/K) ≃ₜ* Gal(SeparableClosure K/K) =>
      TopologicalAbelianization.congr φ) hGalois

end NativeFields

namespace RayClass

section FieldIsomorphism

variable {k : Type u} {K : Type v} {F : Type w}
  [Field k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] (τ : K ≃ₐ[k] F)

/-- The place restriction attached to the original field isomorphism is
the original restriction for its literal coefficient map. -/
def fieldIsoPlaceRestrict (w : Place k F) : Place k K := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  have : IsScalarTower k K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ.commutes x).symm)
  let e := fieldIsoAsAlgEquiv τ.toRingEquiv
  have : FiniteDimensional K F :=
    FiniteDimensional.of_surjective e.toLinearMap e.surjective
  exact w.restrict K

/-- The isomorphism place has the literal inverse-image valuation ring. -/
theorem fieldIsoPlaceRestrict_toValuationSubring (w : Place k F) :
    (fieldIsoPlaceRestrict τ w).toValuationSubring =
      w.toValuationSubring.comap τ.toRingHom := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  have : IsScalarTower k K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ.commutes x).symm)
  let e := fieldIsoAsAlgEquiv τ.toRingEquiv
  have : FiniteDimensional K F :=
    FiniteDimensional.of_surjective e.toLinearMap e.surjective
  change (w.restrict K).toValuationSubring = _
  rw [Place.restrict_toValuationSubring]
  rfl

/-- Pull back the actual original modulus through the specified field
isomorphism, using its literal restriction of places. -/
def fieldIsoRayModulus (m : Modulus k K) : Modulus k F := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  have : IsScalarTower k K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ.commutes x).symm)
  let e := fieldIsoAsAlgEquiv τ.toRingEquiv
  have : FiniteDimensional K F :=
    FiniteDimensional.of_surjective e.toLinearMap e.surjective
  exact rayModulusBaseChange F m

/-- The isomorphism modulus has precisely its original pulled-back coefficient. -/
theorem fieldIsoRayModulus_apply (m : Modulus k K) (w : Place k F) :
    fieldIsoRayModulus τ m w = m (fieldIsoPlaceRestrict τ w) := rfl

variable (m : Modulus k K) (n : Modulus k F)
  (hm : ∀ v, m v ≤ 1) (hn : fieldIsoRayModulus τ m = n)

/-- The actual completion-induced restricted-product map of the original
field isomorphism, into the specified target modulus. -/
def fieldIsoRestrictedRayHom : RayRestrictedProduct m →* RayRestrictedProduct n := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  have : IsScalarTower k K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ.commutes x).symm)
  let e := fieldIsoAsAlgEquiv τ.toRingEquiv
  have : FiniteDimensional K F :=
    FiniteDimensional.of_surjective e.toLinearMap e.surjective
  exact (rayModulusCongr hn).toMonoidHom.comp (restrictedRayBaseChange (L := F) m hm)

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]

/-- Every original principal function has its specified actual field image. -/
theorem fieldIsoRestrictedRayHom_principal (x : Kˣ) :
    fieldIsoRestrictedRayHom τ m n hm hn (principalToRayRestrictedProduct m x) =
      principalToRayRestrictedProduct n (Units.map τ.toRingHom x) := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  have : IsScalarTower k K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ.commutes x).symm)
  let e := fieldIsoAsAlgEquiv τ.toRingEquiv
  have : FiniteDimensional K F :=
    FiniteDimensional.of_surjective e.toLinearMap e.surjective
  change rayModulusCongr hn
    (restrictedRayBaseChange (L := F) m hm (principalToRayRestrictedProduct m x)) = _
  let y : Fˣ := Units.map τ.toRingHom x
  have hBase :
      restrictedRayBaseChange (L := F) m hm (principalToRayRestrictedProduct m x) =
        principalToRayRestrictedProduct (fieldIsoRayModulus τ m) y :=
    restrictedRayBaseChange_principal m hm x
  exact (congrArg (rayModulusCongr hn) hBase).trans
    (rayModulusCongr_principal hn y)

variable [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (a : SeparableClosure K ≃+* SeparableClosure F)
  (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
    algebraMap F (SeparableClosure F) (τ x))

/-- The native ray homomorphism induced by the specified original field
and closure isomorphisms. Original reciprocity proves it is well defined. -/
def fieldIsoNativeRayHom :
    (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) →ₜ*
      (localAbsoluteAbelianProfinite F ⧸ artinRaySubgroup n) := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  have : IsScalarTower k K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ.commutes x).symm)
  let e := fieldIsoAsAlgEquiv τ.toRingEquiv
  have : FiniteDimensional K F :=
    FiniteDimensional.of_surjective e.toLinearMap e.surjective
  have : IsGalois K F := IsGalois.of_algEquiv e
  have hdegree : Module.finrank K F = 1 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  let : Algebra K (SeparableClosure F) :=
    ((algebraMap F (SeparableClosure F)).comp τ.toRingHom).toAlgebra
  have : IsScalarTower K F (SeparableClosure F) := IsScalarTower.of_algebraMap_eq' rfl
  exact degreeOneRayHom k K F hdegree
    (fieldIsoClosureBackEquiv τ.toRingEquiv a ha) m n hm hn

/-- The ray map keeps exactly the native absolute conjugation on every
original abelian representative. -/
theorem fieldIsoNativeRayHom_mk (z : localAbsoluteAbelianProfinite K) :
    fieldIsoNativeRayHom τ m n hm hn a ha (QuotientGroup.mk' (artinRaySubgroup m) z) =
      QuotientGroup.mk' (artinRaySubgroup n) (nativeFieldIsoAbelianEquiv τ.toRingEquiv a ha z) :=
  rfl

/-- The original native ray map and the actual completion-induced field
map satisfy the same reciprocity square. -/
theorem fieldIsoNativeRayHom_artin (x : RayRestrictedProduct m) :
    restrictedProductAbsoluteArtin n (fieldIsoRestrictedRayHom τ m n hm hn x) =
      fieldIsoNativeRayHom τ m n hm hn a ha (restrictedProductAbsoluteArtin m x) := by
  let : Algebra K F := τ.toRingHom.toAlgebra
  have : IsScalarTower k K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ.commutes x).symm)
  let e := fieldIsoAsAlgEquiv τ.toRingEquiv
  have : FiniteDimensional K F :=
    FiniteDimensional.of_surjective e.toLinearMap e.surjective
  have : IsGalois K F := IsGalois.of_algEquiv e
  have hdegree : Module.finrank K F = 1 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  let : Algebra K (SeparableClosure F) :=
    ((algebraMap F (SeparableClosure F)).comp τ.toRingHom).toAlgebra
  have : IsScalarTower K F (SeparableClosure F) := IsScalarTower.of_algebraMap_eq' rfl
  exact restrictedProductAbsoluteArtin_degreeOne k K F hdegree
    (fieldIsoClosureBackEquiv τ.toRingEquiv a ha) m n hm hn x

end FieldIsomorphism

section CoverAutomorphism

variable {k : Type u} {K : Type v} {L : Type w}
  [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L]
  (τ : L ≃ₐ[K] L)

/-- A genuine covering-field automorphism leaves the original restricted
place unchanged; this follows from its actual coefficient action. -/
theorem fieldIsoPlaceRestrict_restrict_of_fixed (w : Place k L) :
    (fieldIsoPlaceRestrict (τ.restrictScalars k) w).restrict K = w.restrict K := by
  apply Place.ext
  rw [Place.restrict_toValuationSubring, fieldIsoPlaceRestrict_toValuationSubring,
    Place.restrict_toValuationSubring]
  apply ValuationSubring.ext
  intro x
  change τ (algebraMap K L x) ∈ w.toValuationSubring ↔
    algebraMap K L x ∈ w.toValuationSubring
  rw [τ.commutes]

/-- Pulling back an original modulus to an actual finite cover makes it
invariant under every genuine automorphism of that cover. -/
theorem fieldIsoRayModulus_baseChange_of_fixed (m : Modulus k K) :
    fieldIsoRayModulus (τ.restrictScalars k) (rayModulusBaseChange L m) =
      rayModulusBaseChange L m := by
  apply Finsupp.ext
  intro w
  rw [fieldIsoRayModulus_apply]
  change m ((fieldIsoPlaceRestrict (τ.restrictScalars k) w).restrict K) =
    m (w.restrict K)
  rw [fieldIsoPlaceRestrict_restrict_of_fixed]

end CoverAutomorphism

end RayClass

end FunctionField
