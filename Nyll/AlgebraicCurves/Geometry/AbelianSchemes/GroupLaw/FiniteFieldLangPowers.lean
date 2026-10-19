/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLangNorm
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangIterate

/-!
# Lang surjectivity and norms for powers of Frobenius

All positive powers of the actual finite-field Frobenius have surjective Lang
operators. This gives norm preimages fixed by the prescribed Frobenius power.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of k))]
    (L : RelativeGroupLaw k (X ↘ Spec (CommRingCat.of k))) (hc : L.IsCommutative)

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "g" => pullback.snd f b

omit [IsAlgClosed Ω] in
/-- Iteration of the geometric Frobenius agrees with powers of the actual Galois action. -/
theorem finiteFieldGeometricPoint_frobenius_npow (n : ℕ)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g) :
    finiteFieldGeometricPoint k Ω X L hc
        (NeronModelInfra.schemeHomOverComp x
          (schemeHomOverNpow (finiteFieldFrobeniusOver k Ω X) n)) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ n •
        finiteFieldGeometricPoint k Ω X L hc x := by
  induction n with
  | zero =>
    exact (congrArg (finiteFieldGeometricPoint k Ω X L hc)
      (NeronModelInfra.schemeHomOverComp_id_right x)).trans
        (one_smul _ _).symm
  | succ n ih =>
    have hcomp := NeronModelInfra.schemeHomOverComp_assoc x
      (schemeHomOverNpow (finiteFieldFrobeniusOver k Ω X) n)
      (finiteFieldFrobeniusOver k Ω X)
    have hpoint := finiteFieldGeometricPoint_frobenius k Ω X L hc
      (NeronModelInfra.schemeHomOverComp x
        (schemeHomOverNpow (finiteFieldFrobeniusOver k Ω X) n))
    refine (congrArg (finiteFieldGeometricPoint k Ω X L hc) hcomp.symm).trans
      (hpoint.trans ?_)
    rw [ih, pow_succ', mul_smul]

/-- Every positive Frobenius power minus the identity is surjective on actual algebraic points. -/
theorem surjective_frobenius_pow_sub
    (hX : AbelianSchemePropertyBundle k (X ↘ Spec (CommRingCat.of k)))
    (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x : L.AlgPoints hc Ω =>
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ n • x - x) := by
  intro y
  obtain ⟨y', hy⟩ := finiteFieldGeometricPoint_surjective k Ω X L hc y
  let π := finiteFieldFrobeniusOver k Ω X
  obtain ⟨x, hx⟩ := surjective_langMap_npow_points π
    (Scheme.constantBaseChangeFrobenius_map_maximalIdeal_le_sq k Ω X)
    (L.baseChange b) (hc.baseChange b) (hX.baseChange_of_field b) n hn y'
  refine ⟨finiteFieldGeometricPoint k Ω X L hc x, ?_⟩
  have he := (finiteFieldGeometricPoint_langMap_apply k Ω X L hc
    (schemeHomOverNpow π n) x).trans
      (congrArg (· - finiteFieldGeometricPoint k Ω X L hc x)
        (finiteFieldGeometricPoint_frobenius_npow k Ω X L hc n x))
  exact he.symm.trans ((congrArg (finiteFieldGeometricPoint k Ω X L hc) hx).trans hy)

/-- Every Frobenius-fixed point is the norm of a point fixed by a prescribed positive power. -/
theorem exists_frobenius_periodic_norm_preimage
    (hX : AbelianSchemePropertyBundle k (X ↘ Spec (CommRingCat.of k)))
    (n : ℕ) (hn : n ≠ 0) (y : L.AlgPoints hc Ω)
    (hy : FiniteField.frobeniusAlgEquivOfAlgebraic k Ω • y = y) :
    ∃ x : L.AlgPoints hc Ω,
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ n • x = x ∧
        ∑ i ∈ Finset.range n, (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ i • x = y :=
  CyclicAction.exists_fixed_norm_preimage_of_surjective_sub_pow _ n
    (surjective_frobenius_pow_sub k Ω X L hc hX n hn) y hy

end GoodReductionJacobian.RelativeGroupLaw
