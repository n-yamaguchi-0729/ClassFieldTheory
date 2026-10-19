/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.NormDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegreeSurjective
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.IntegerValueGroup

/-!
# Integral degree on the actual base fixed coefficients

The actual fixed-field comparison transports normalized idele degree to the
base fixed module. Its image in the profinite integers is precisely the
integer value group. Rational degree computes its values on abstract norms.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The integral normalized degree of the actual base fixed coefficients. -/
def ideleClassBaseIntegerDegree :
    ambientFixedAddSubgroup (ideleClassRepresentation k K Ω) (baseField Gal(Ω/K)) →+ ℤ := by
  have hE : FiniteDimensional K (abstractFixedField K Ω (baseField Gal(Ω/K))) :=
    abstractFixedField_finiteDimensional K Ω _ (FiniteAbstractField.base Gal(Ω/K)).finite
  exact (MonoidHom.toAdditiveLeft
    (IdeleClassGroup.normalizedDegree (k := k)
      (K := abstractFixedField K Ω (baseField Gal(Ω/K))))).comp
        (abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K))
          (FiniteAbstractField.base Gal(Ω/K)).finite).symm.toAddMonoidHom

/-- Every integer is realized by an actual base fixed coefficient. -/
theorem ideleClassBaseIntegerDegree_surjective :
    Function.Surjective (ideleClassBaseIntegerDegree k K Ω) := by
  have hE : FiniteDimensional K (abstractFixedField K Ω (baseField Gal(Ω/K))) :=
    abstractFixedField_finiteDimensional K Ω _ (FiniteAbstractField.base Gal(Ω/K)).finite
  intro n
  obtain ⟨c, hc⟩ := IdeleClassGroup.normalizedDegree_surjective
    (k := k) (K := abstractFixedField K Ω (baseField Gal(Ω/K))) (Multiplicative.ofAdd n)
  refine ⟨abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K))
          (FiniteAbstractField.base Gal(Ω/K)).finite
    (Additive.ofMul c), ?_⟩
  change (IdeleClassGroup.normalizedDegree (k := k)
    (K := abstractFixedField K Ω (baseField Gal(Ω/K)))
      (((abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K))
          (FiniteAbstractField.base Gal(Ω/K)).finite).symm
        (abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K))
          (FiniteAbstractField.base Gal(Ω/K)).finite
          (Additive.ofMul c))).toMul)).toAdd = n
  rw [AddEquiv.symm_apply_apply]
  exact congrArg Multiplicative.toAdd hc

/-- Normalized degree with its values in the actual profinite integers. -/
def ideleClassBaseDegree :
    ambientFixedAddSubgroup (ideleClassRepresentation k K Ω) (baseField Gal(Ω/K)) →+ ZHat :=
  (Int.castRingHom ZHat).toAddMonoidHom.comp (ideleClassBaseIntegerDegree k K Ω)

/-- Its actual value group is the image of the integers. -/
theorem ideleClassBaseDegree_range :
    (ideleClassBaseDegree k K Ω).range = integerValueGroup := by
  apply AddSubgroup.ext
  intro z
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨ideleClassBaseIntegerDegree k K Ω c, rfl⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨c, hc⟩ := ideleClassBaseIntegerDegree_surjective k K Ω n
    exact ⟨c, congrArg (fun m : ℤ => (m : ZHat)) hc⟩

/-- Reduction of actual base values induces the canonical quotient isomorphism. -/
theorem ideleClassBaseDegree_quotient_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (canonicalValueQuotientMap (ideleClassBaseDegree k K Ω).range n hn) := by
  rw [ideleClassBaseDegree_range]
  exact canonicalValueQuotientMap_integer_bijective n hn

/-- The full constant factor recovers rational degree on the base fixed module. -/
theorem fullConstants_mul_ideleClassBaseIntegerDegree
    (c : ambientFixedAddSubgroup (ideleClassRepresentation k K Ω) (baseField Gal(Ω/K))) :
    (Module.finrank k (algebraicClosure k K) : ℚ) *
        (ideleClassBaseIntegerDegree k K Ω c : ℚ) =
      ideleClassRationalDegree k K Ω c.1 := by
  have hE : FiniteDimensional K (abstractFixedField K Ω (baseField Gal(Ω/K))) :=
    abstractFixedField_finiteDimensional K Ω _ (FiniteAbstractField.base Gal(Ω/K)).finite
  have hbot : abstractFixedField K Ω (baseField Gal(Ω/K)) = ⊥ :=
    InfiniteGalois.fixedField_bot
  have hdegree : Module.finrank K (abstractFixedField K Ω (baseField Gal(Ω/K))) = 1 := by
    rw [hbot, IntermediateField.finrank_bot]
  let e : abstractFixedField K Ω (baseField Gal(Ω/K)) ≃ₐ[K] K :=
    (IntermediateField.equivOfEq hbot).trans (IntermediateField.botEquiv K Ω)
  have hconstants : Module.finrank k
      (algebraicClosure k (abstractFixedField K Ω (baseField Gal(Ω/K)))) =
        Module.finrank k (algebraicClosure k K) :=
    (e.restrictScalars k).algebraicClosure.toLinearEquiv.finrank_eq
  obtain ⟨a, rfl⟩ :=
    (abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K))
          (FiniteAbstractField.base Gal(Ω/K)).finite).surjective c
  have hd := ideleClassRationalDegree_abstractFixedClassEquiv k K Ω
    (baseField Gal(Ω/K)) (FiniteAbstractField.base Gal(Ω/K)).finite a
  rw [hdegree, Nat.cast_one, div_one] at hd
  apply Eq.trans _ hd.symm
  change (Module.finrank k (algebraicClosure k K) : ℚ) *
    ((IdeleClassGroup.normalizedDegree (k := k)
      (K := abstractFixedField K Ω (baseField Gal(Ω/K)))
        (((abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K))
          (FiniteAbstractField.base Gal(Ω/K)).finite).symm
          (abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K))
          (FiniteAbstractField.base Gal(Ω/K)).finite a)).toMul)).toAdd : ℚ) = _
  rw [AddEquiv.symm_apply_apply, ← hconstants]
  exact_mod_cast (IdeleClassGroup.fullConstants_mul_normalizedDegree a.toMul)

/-- Abstract norms retain exactly the actual upper-field degree before normalization. -/
theorem fullConstants_mul_ideleClassBaseIntegerDegree_norm (H : FiniteAbstractField Gal(Ω/K)) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω H.field)),
      (Module.finrank k (algebraicClosure k K) : ℤ) *
        ideleClassBaseIntegerDegree k K Ω
          (normToBase (ideleClassRepresentation k K Ω) H.field
            (abstractFixedClassEquiv k K Ω H.field H.finite c)) =
        (IdeleClassGroup.degree (k := k) (K := abstractFixedField K Ω H.field) c.toMul).toAdd := by
  intro hE c
  have h := fullConstants_mul_ideleClassBaseIntegerDegree k K Ω
    (normToBase (ideleClassRepresentation k K Ω) H.field
      (abstractFixedClassEquiv k K Ω H.field H.finite c))
  rw [ideleClassRationalDegree_normToBase] at h
  exact_mod_cast h

end FunctionField
