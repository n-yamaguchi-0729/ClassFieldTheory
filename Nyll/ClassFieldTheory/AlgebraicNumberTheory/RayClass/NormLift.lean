/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Norm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.LocalNormBound
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction

/-!
# A compatible full modulus for the actual norm

The explicit safe depths `e * (m - 1) + 1`, with positivity at all real
places upstairs, give a full modulus for which the actual ray norm is
defined. Outside the downstairs support the depth stays zero.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

namespace RayClass

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- At depth zero the norm preserves integral units; no positive depth is
needed. The completion algebra is the actual map at the specified place. -/
theorem localHigherUnitGroup_zero_le_norm_preimage
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v}) :
    let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (_root_.finitePlaceAdicCompletionMap K L v W).toAlgebra
    ClassFieldTheory.rayLocalHigherUnitGroup W.1 0 ≤
      (ClassFieldTheory.rayLocalHigherUnitGroup v 0).comap
      (LocalFieldTheory.normUnits (v.adicCompletion K) (W.1.adicCompletion L)) := by
  intro completionAlgebra
  rw [ClassFieldTheory.rayLocalHigherUnitGroup_zero, ClassFieldTheory.rayLocalHigherUnitGroup_zero]
  intro x hx
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v _).mp
  rw [FiniteIdeleGroup.localOrder_normUnits K L v W,
    (FiniteIdeleGroup.localOrder_eq_zero_iff W.1 x).mpr hx, mul_zero]

/-- The explicit safe local depth, with zero preserved outside the original support. -/
noncomputable def normLiftedModulusExponent (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) : ℕ :=
  if m.finitePart (finitePlaceBelow (K := K) W) = 0 then 0 else
    W.asIdeal.ramificationIdx (𝓞 K) *
        (m.finitePart (finitePlaceBelow (K := K) W) - 1) + 1

/-- A full norm-compatible modulus with explicit safe finite exponents and
positivity at every real place upstairs. -/
noncomputable def normLiftedModulus (m : Modulus K) : Modulus L := by
  classical
  refine Modulus.narrowOfFinite
    (Finsupp.ofSupportFinite (normLiftedModulusExponent (L := L) m) ?_)
  refine (Set.Finite.preimage_finitePlaceBelow (L := L)
    m.finitePart.support.finite_toSet).subset ?_
  intro W hW
  by_contra hnot
  have hzero := Finsupp.notMem_support_iff.mp hnot
  exact hW (by rw [normLiftedModulusExponent, ite_eq_left hzero])

omit [FiniteDimensional K L] in
/-- The constructed finite coefficients are the stated arithmetic safe depths. -/
theorem normLiftedModulus_finitePart_apply (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    (normLiftedModulus (L := L) m).finitePart W =
      if m.finitePart (finitePlaceBelow (K := K) W) = 0 then 0 else
        W.asIdeal.ramificationIdx (𝓞 K) *
            (m.finitePart (finitePlaceBelow (K := K) W) - 1) + 1 := rfl

omit [FiniteDimensional K L] in
/-- The full norm lift keeps depth zero outside the downstairs support. -/
theorem normLiftedModulus_finitePart_eq_zero
    (m : Modulus K) (W : HeightOneSpectrum (𝓞 L))
    (hW : m.finitePart (_root_.finitePlaceBelow (K := K) W) = 0) :
    (normLiftedModulus (L := L) m).finitePart W = 0 := by
  rw [normLiftedModulus_finitePart_apply, ite_eq_left hW]

/-- All local hypotheses for norm descent hold for the constructed full
modulus. The positive-depth case uses the finite separable norm bound, and
the zero-depth case uses preservation of integral units. -/
theorem normLiftedModulus_normCompatible (m : Modulus K) :
    (normLiftedModulus (L := L) m).NormCompatible m := by
  constructor
  · rintro v ⟨W, rfl⟩
    intro completionAlgebra
    by_cases hzero : m.finitePart (finitePlaceBelow (K := K) W) = 0
    · rw [normLiftedModulus_finitePart_eq_zero m W hzero, hzero]
      exact localHigherUnitGroup_zero_le_norm_preimage
        (_root_.finitePlaceBelow (K := K) W) ⟨W, rfl⟩
    · rw [normLiftedModulus_finitePart_apply, ite_eq_right hzero]
      exact localHigherUnitGroup_le_norm_preimage_of_depth K L
        (finitePlaceBelow (K := K) W) ⟨W, rfl⟩ (Nat.lt_succ_self _)
  · intro v hv W hW
    classical
    change (⟨W.1, hW⟩ : RealPlace L) ∈ Finset.univ
    exact Finset.mem_univ _

/-- Every full modulus admits a full modulus upstairs on which the actual
norm descends, without any additional local compatibility assumption. -/
theorem exists_normCompatible_modulus (m : Modulus K) :
    ∃ n : Modulus L, n.NormCompatible m :=
  ⟨normLiftedModulus (L := L) m, normLiftedModulus_normCompatible m⟩

end RayClass
