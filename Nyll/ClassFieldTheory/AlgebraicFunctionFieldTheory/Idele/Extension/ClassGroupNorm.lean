/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Finset.Image
import Mathlib.GroupTheory.QuotientGroup.Defs
import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore

/-!
# Norm on function-field idele classes

The completed norm product is the actual global field norm on diagonal elements.
Consequently the all-place idele norm carries principal ideles to principal ideles
and induces a homomorphism of idele class groups.
-/

open scoped AlgebraicCurve.Place

noncomputable section

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k L]

namespace IdeleGroup

private theorem coe_localNormOver_principal (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (hw : w.restrict K = v) (x : Lˣ) :
    (localNormOver v w hw ((principalIdele k L x) w) : v.adicCompletion) =
      cast (congrArg (fun u : AlgebraicCurve.Place k K => u.adicCompletion) hw)
        (Algebra.norm (w.restrict K).adicCompletion
          (algebraMap L w.adicCompletion (x : L))) := by
  subst v
  rfl

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The all-place idele norm sends a diagonal function to its global field norm. -/
@[simp]
theorem norm_principalIdele (x : Lˣ) :
    norm (K := K) (L := L) (principalIdele k L x) =
      principalIdele k K (Units.map (Algebra.norm K) x) := by
  classical
  apply RestrictedProduct.ext
  intro v
  apply Units.ext
  change (normComponent (k := k) (K := K) (L := L) v (principalIdele k L x) :
    v.adicCompletion) = algebraMap K v.adicCompletion (Algebra.norm K (x : L))
  rw [normComponent_apply, Units.coe_prod,
    AlgebraicCurve.completionNormProduct_of_isSeparable v (x : L)]
  let e : v.fiberOver L ≃ v.fiber L :=
    Finset.equivOfEq (AlgebraicCurve.Place.fiber_eq_fiberOver v).symm
  refine Fintype.prod_equiv e _ _ ?_
  intro w
  exact coe_localNormOver_principal v w.1
    ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) x

/-- The norm preserves the subgroup of principal ideles. -/
theorem norm_mem_principalSubgroup {a : IdeleGroup k L}
    (ha : a ∈ principalSubgroup k L) :
    norm (K := K) (L := L) a ∈ principalSubgroup k K := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨Units.map (Algebra.norm K) x, (norm_principalIdele x).symm⟩

end IdeleGroup

namespace IdeleClassGroup

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The field norm on idele classes, descended through the actual principal subgroup. -/
def norm : IdeleClassGroup k L →* IdeleClassGroup k K :=
  QuotientGroup.map (IdeleGroup.principalSubgroup k L) (IdeleGroup.principalSubgroup k K)
    (IdeleGroup.norm (K := K) (L := L))
    (fun _ ha => IdeleGroup.norm_mem_principalSubgroup ha)

@[simp]
theorem norm_mk (a : IdeleGroup k L) :
    norm (K := K) (L := L) (QuotientGroup.mk a) =
      QuotientGroup.mk (IdeleGroup.norm (K := K) (L := L) a) :=
  rfl

end IdeleClassGroup

end FunctionField
