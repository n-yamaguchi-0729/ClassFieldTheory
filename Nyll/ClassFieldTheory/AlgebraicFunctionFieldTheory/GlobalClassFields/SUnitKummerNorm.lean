/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitPowerClassSubgroup
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitKummerUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SupportedComponents

/-!
# The actual S-unit Kummer norm subgroup

Power components on S contribute class norms because the actual Galois group
has exponent dividing n. Integral components outside S have actual local norm
preimages by unramifiedness. The calculated indices then give equality with
the actual norm subgroup of the S-unit root field.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.SUnits

open IdeleGroup KummerTheory

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

private theorem powerClassSubgroup_le_norm_of_exponent
    {E : Type} [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional K E] [IsAbelianGalois K E] [HasPrincipalDivisors k E]
    (n : ℕ+) (S : Finset (Place k K))
    (hpow : ∀ σ : Gal(E/K), σ ^ (n : ℕ) = 1)
    (hAway : ∀ w : Place k E, w.restrict K ∉ S → w.ramificationIndex K = 1) :
    powerClassSubgroup n S ≤ (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range := by
  classical
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K E
  let aRE : Algebra (RatFunc k) E := presentation.val
  have hkRE : IsScalarTower k (RatFunc k) E := presentation.property.1
  have hEfunction : FunctionField k E := presentation.property.2
  intro c hc
  obtain ⟨a, ha, rfl⟩ := hc
  have hroots (v : S) : ∃ x : v.val.adicCompletionˣ, x ^ (n : ℕ) = a.val v.val := by
    have hz := congrFun ha v
    change QuotientGroup.mk' (powMonoidHom (α := v.val.adicCompletionˣ) (n : ℕ)).range
      (a.val v.val) = 1 at hz
    exact (QuotientGroup.eq_one_iff _).mp hz
  choose x hx using hroots
  obtain ⟨bS, hbin, hbout⟩ := exists_supported_sIdele S x
  let b : IdeleGroup k K := bS.val
  let d : IdeleGroup k K := a.val / b ^ (n : ℕ)
  choose w hw using fun v : Place k K => Place.exists_restrict_eq (M := E) v
  have hpre (v : Place k K) : ∃ z : IdeleGroup k E,
      normComponent (k := k) (K := K) (L := E) v z = d v ∧
      fiberProjection (L := E) v z ∈ fiberIntegralUnits (L := E) v := by
    by_cases hv : v ∈ S
    · have hd : d v = 1 := by
        change a.val v / (bS.val v) ^ (n : ℕ) = 1
        rw [hbin ⟨v, hv⟩, hx ⟨v, hv⟩]
        exact div_self' (a.val v)
      exact ⟨1, (map_one _).trans hd.symm, by
        rw [map_one]
        exact Subgroup.one_mem _⟩
    · have hd : d v = a.val v := by
        change a.val v / (bS.val v) ^ (n : ℕ) = a.val v
        rw [hbout v hv, one_pow, div_one]
      have he : (w v).ramificationIndex K = 1 := hAway (w v) (by rw [hw v]; exact hv)
      obtain ⟨y, hyint, hy⟩ := exists_integral_localNormOver_eq_of_ramificationIndex_eq_one
        v (w v) (hw v) he (a.val v) (a.property v hv)
      exact ⟨placeIdele (w v) y,
        (normComponent_placeIdele v (w v) (hw v) y).trans (hy.trans hd.symm),
        fiberProjection_placeIdele_mem_integral v (w v) y hyint⟩
  choose z hz hzi using hpre
  obtain ⟨y, hy⟩ := mem_norm_range_of_normComponent_preimages d z hz
    (Filter.Eventually.of_forall hzi)
  have hdNorm : IdeleClassGroup.mk (k := k) (K := K) d ∈
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range :=
    ⟨IdeleClassGroup.mk (k := k) (K := E) y, congrArg (IdeleClassGroup.mk (k := k) (K := K)) hy⟩
  have hbNorm : (IdeleClassGroup.mk (k := k) (K := K) b) ^ (n : ℕ) ∈
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range := by
    apply (abelianFiniteArtin_eq_one_iff_mem_norm k K E _).mp
    rw [map_pow]
    exact hpow _
  have hfactor : sIdeleClass S a =
      (IdeleClassGroup.mk (k := k) (K := K) d) *
        (IdeleClassGroup.mk (k := k) (K := K) b) ^ (n : ℕ) := by
    rw [← map_pow, ← map_mul]
    change IdeleClassGroup.mk (k := k) (K := K) a.val =
      IdeleClassGroup.mk (k := k) (K := K) ((a.val / b ^ (n : ℕ)) * b ^ (n : ℕ))
    rw [div_mul_cancel]
  rw [hfactor]
  exact Subgroup.mul_mem _ hdNorm hbNorm

/-- The actual S-unit Kummer extension has exactly the power-component class
subgroup as its norm image. All extension structures are constructed. -/
theorem kummerExtension_norm_range {Ω : Type} [Field Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω] [IsSepClosure K Ω]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (S : Finset (Place k K))
    (hSne : S.Nonempty) (hS : Function.Surjective (sIdeleClass S)) :
    let E := kummerExtension (Ω := Ω) n S
    let _ : FiniteDimensional K E := kummerExtension_finiteDimensional n hn hmu S
    let _ : IsCurveOver k E :=
      ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E
    (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range = powerClassSubgroup n S := by
  intro E _ _
  have hEabelian : IsAbelianGalois K E := kummerRadicalExtension_isAbelianGalois n hmu (units k K S)
  have hle : powerClassSubgroup n S ≤
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range :=
    powerClassSubgroup_le_norm_of_exponent (k := k) (K := K) (E := E) n S
      (kummerRadicalExtension_galois_pow_eq_one n hmu (units k K S))
      (kummerExtension_ramificationIndex_eq_one n hn hmu S)
  have hNindex : (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range.index =
      (n : ℕ) ^ S.card :=
    (Nat.card_congr (abelianFiniteNormQuotientEquiv k K E).toEquiv).trans
      ((IsGalois.card_aut_eq_finrank K E).trans (kummerExtension_finrank n hn hmu S hSne))
  have hPindex := index_powerClassSubgroup n hn hmu S hSne hS
  have hmul := Subgroup.relIndex_mul_index hle
  rw [hNindex, hPindex] at hmul
  have hrel : (powerClassSubgroup n S).relIndex
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range = 1 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos n.pos S.card) (hmul.trans (one_mul _).symm)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hle

end FunctionField.SUnits
