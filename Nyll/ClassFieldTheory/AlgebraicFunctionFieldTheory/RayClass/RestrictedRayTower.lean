/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Coherence of the original restricted-ray transitions

Pulling a reduced boundary through a field tower agrees with its direct pullback.
After this literal equality of moduli, the actual restricted-product transitions
compose. The proof uses representatives in the original idele groups and the
proved composition law of the completion inclusions.

The resulting identity and composition laws hold on the native absolute-Artin
kernels, including at zero modulus. They provide the transition laws needed for
the finite constant-extension system without defining maps through recovered
function groups.
-/

@[expose] public section

universe u v w x

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

section ModulusCongruence

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Equality of boundary exponents identifies the original restricted local factors. -/
def rayModulusCongr {m n : Modulus k K} (h : m = n) :
    RayRestrictedProduct m ≃* RayRestrictedProduct n :=
  MulEquiv.cast (M := fun m : Modulus k K => RayRestrictedProduct m) h

/-- Modulus transport retains the original idele representative. -/
theorem rayModulusCongr_idele {m n : Modulus k K} (h : m = n) (a : IdeleGroup k K) :
    rayModulusCongr h (ideleToRayRestrictedProduct m a) = ideleToRayRestrictedProduct n a := by
  subst n
  rfl

variable [HasPrincipalDivisors k K] in
/-- Modulus transport retains every original principal function. -/
theorem rayModulusCongr_principal {m n : Modulus k K} (h : m = n) (x : Kˣ) :
    rayModulusCongr h (principalToRayRestrictedProduct m x) =
      principalToRayRestrictedProduct n x := by
  subst n
  rfl

/-- Pullback through the identity extension leaves the actual modulus unchanged. -/
theorem rayModulusBaseChange_self (m : Modulus k K) : rayModulusBaseChange K m = m := by
  apply Finsupp.ext
  intro v
  change m (v.restrict K) = m v
  apply congrArg m
  apply Place.ext
  rw [Place.restrict_toValuationSubring]
  exact ValuationSubring.ext _ _ fun _ => Iff.rfl

/-- The actual restricted-ray inclusion of the identity field extension is identity. -/
theorem restrictedRayBaseChange_self (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (a : RayRestrictedProduct m) :
    rayModulusCongr (rayModulusBaseChange_self m)
      (restrictedRayBaseChange (L := K) m hm a) = a := by
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  rw [restrictedRayBaseChange_idele, rayModulusCongr_idele, IdeleGroup.baseChange_self]

end ModulusCongruence

section FieldTower

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

/-- Pullback retains the reduced exponents with their literal modulus type. -/
theorem rayModulusBaseChange_reduced (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (w : Place k L) : rayModulusBaseChange L m w ≤ 1 :=
  hm (w.restrict K)

/-- Iterated pullback has exactly the same exponents as direct pullback. -/
theorem rayModulusBaseChange_trans (m : Modulus k K) :
    rayModulusBaseChange M (rayModulusBaseChange L m) = rayModulusBaseChange M m := by
  apply Finsupp.ext
  intro w
  change m ((w.restrict L).restrict K) = m (w.restrict K)
  exact congrArg m (restrict_restrict (F := K) (E := L) w)

/-- The original completion-induced maps compose after the literal boundary equality. -/
theorem restrictedRayBaseChange_trans (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (a : RayRestrictedProduct m) :
    rayModulusCongr (rayModulusBaseChange_trans (L := L) (M := M) m)
        (restrictedRayBaseChange (L := M) (rayModulusBaseChange L m)
          (rayModulusBaseChange_reduced m hm) (restrictedRayBaseChange (L := L) m hm a)) =
      restrictedRayBaseChange (L := M) m hm a := by
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  have hinner := restrictedRayBaseChange_idele (L := L) m hm b
  have houter := restrictedRayBaseChange_idele (L := M) (rayModulusBaseChange L m)
    (rayModulusBaseChange_reduced m hm) (IdeleGroup.baseChange (K := K) (L := L) b)
  rw [hinner, houter, rayModulusCongr_idele, IdeleGroup.baseChange_trans,
    restrictedRayBaseChange_idele]

end FieldTower

section KernelCongruence

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- Equal boundary exponents identify the kernels of the same original Artin map. -/
def principalArtinKernelCongr {m n : Modulus k K} (h : m = n) :
    (restrictedProductAbsoluteArtin m).ker ≃* (restrictedProductAbsoluteArtin n).ker :=
  MulEquiv.cast (M := fun m : Modulus k K => (restrictedProductAbsoluteArtin m).ker) h

/-- Kernel transport is the identical transport of the original restricted local family. -/
theorem principalArtinKernelCongr_coe {m n : Modulus k K} (h : m = n)
    (a : (restrictedProductAbsoluteArtin m).ker) :
    (principalArtinKernelCongr h a : RayRestrictedProduct n) =
      rayModulusCongr h (a : RayRestrictedProduct m) := by
  subst n
  rfl

/-- The native kernel inclusion of the identity extension fixes every kernel element. -/
theorem principalArtinKernelBaseChange_self (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (a : (restrictedProductAbsoluteArtin m).ker) :
    principalArtinKernelCongr (rayModulusBaseChange_self m)
      (principalArtinKernelBaseChange (L := K) m hm a) = a := by
  apply Subtype.ext
  rw [principalArtinKernelCongr_coe]
  exact restrictedRayBaseChange_self m hm a.val

end KernelCongruence

section KernelTower

variable {k : Type u} {K : Type v} {L : Type w} {M : Type x}
    [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M] [FunctionField k M]

/-- Native Artin-kernel transitions compose through every actual finite field tower. -/
theorem principalArtinKernelBaseChange_trans (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (a : (restrictedProductAbsoluteArtin m).ker) :
    principalArtinKernelCongr (rayModulusBaseChange_trans (L := L) (M := M) m)
        (principalArtinKernelBaseChange (L := M) (rayModulusBaseChange L m)
          (rayModulusBaseChange_reduced m hm) (principalArtinKernelBaseChange (L := L) m hm a)) =
      principalArtinKernelBaseChange (L := M) m hm a := by
  apply Subtype.ext
  rw [principalArtinKernelCongr_coe]
  exact restrictedRayBaseChange_trans (L := L) (M := M) m hm a.val

end KernelTower

end FunctionField.RayClass
