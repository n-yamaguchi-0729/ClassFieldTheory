/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveTranscendentalPerfectField
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Restriction.OrderRigidity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ProductFormula
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# The full constant field as the regular functions without poles

A function integral at every place generates a subalgebra that embeds linearly in any one
finite-dimensional residue field. The product formula proves injectivity: a nonzero element
of the kernel would have positive order at that place and no poles anywhere. The subalgebra
is finite-dimensional, so its generator is algebraic over the base field.

Applying this to the existing equivalence of places under integral constant extension proves
`ConstantsAreBase` for the actual relative algebraic closure `algebraicClosure k K`.
-/

@[expose] public section

namespace FunctionField

open AlgebraicCurve

private theorem isAlgebraic_of_forall_mem {k K : Type*} [Field k]
    [Field K] [Algebra k K] [HasPrincipalDivisors k K]
    (P : Place k K) [Module.Finite k P.ResidueField] {f : K}
    (hf : ∀ v : Place k K, f ∈ v.toValuationSubring) : IsAlgebraic k f := by
  classical
  let A : Subalgebra k K := Algebra.adjoin k ({f} : Set K)
  have hA (v : Place k K) (x : A) : (x : K) ∈ v.toValuationSubring := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ x.2
    · intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hf v
    · exact v.algebraMap_mem'
    · intro x y _ _ hx hy
      exact v.toValuationSubring.add_mem x y hx hy
    · intro x y _ _ hx hy
      exact v.toValuationSubring.mul_mem x y hx hy
  let incl : A →+* P.toValuationSubring :=
    A.val.toRingHom.codRestrict P.toValuationSubring.toSubring (hA P)
  let residue : A →ₐ[k] P.ResidueField :=
    { (IsLocalRing.residue P.toValuationSubring).comp incl with
      commutes' a := by
        change IsLocalRing.residue P.toValuationSubring
          (algebraMap k P.toValuationSubring a) = algebraMap k P.ResidueField a
        rw [IsScalarTower.algebraMap_apply k P.toValuationSubring P.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq] }
  have hinj : Function.Injective residue := by
    refine (injective_iff_map_eq_zero residue).2 ?_
    intro x hx
    by_contra hx0
    have hxK : (x : K) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hord : P.ord (x : K) = 0 := ord_eq_zero_of_forall_ord_nonneg P hxK
      (fun v => v.ord_nonneg_of_mem (hA v x))
    have hlog : WithZero.log (P.adicValuation (x : K)) = 0 := neg_eq_zero.mp hord
    have hval : P.adicValuation (x : K) = 1 := by
      rw [← WithZero.exp_log (P.adicValuation_ne_zero hxK), hlog, WithZero.exp_zero]
    have hunit : IsUnit (incl x) := (P.adicValuation_coe_eq_one_iff (incl x)).mp hval
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit (incl x)).2 hunit) hx
  have : Module.Finite k A := Module.Finite.of_injective residue.toLinearMap hinj
  have halg : IsAlgebraic k (⟨f, Algebra.subset_adjoin (Set.mem_singleton f)⟩ : A) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact halg.algHom A.val

variable (k K : Type*) [Field k] [PerfectField k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- Over the actual full constant field, the functions without poles are exactly the scalars. -/
theorem constantsAreBase_fullConstants : ConstantsAreBase (algebraicClosure k K) K := by
  have : IsCurveOver k K := isCurveOver k K
  obtain ⟨P⟩ := nonempty_place k K
  have : Module.Finite k P.ResidueField := IsCurveOver.finiteResidue P
  refine le_antisymm ?_ ?_
  · intro f hf
    have hint (v : Place k K) : f ∈ v.toValuationSubring := by
      rcases eq_or_ne f 0 with rfl | hf0
      · exact v.toValuationSubring.zero_mem
      · have hord := ((mem_lSpace_iff_ord.mp hf).resolve_left hf0)
          (v.extendConstants (algebraicClosure k K))
        simp only [Finsupp.zero_apply, neg_zero] at hord
        exact (v.extendConstants (algebraicClosure k K)).mem_of_ord_nonneg hf0 hord
    have halg : IsAlgebraic k f := isAlgebraic_of_forall_mem P hint
    exact ⟨⟨f, mem_algebraicClosure_iff.mpr halg⟩, rfl⟩
  · rintro f ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

omit [PerfectField k] in
/-- The actual original parameter stays transcendental and finite over the full constants. -/
theorem exists_transcendental_finite_fullConstants :
    ∃ t : K, Transcendental (algebraicClosure k K) t ∧
      FiniteDimensional (IntermediateField.adjoin (algebraicClosure k K) ({t} : Set K)) K := by
  let C := algebraicClosure k K
  let t : K := algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)
  have ht : Transcendental k t :=
    (transcendental_algebraMap_iff (R := k) (S := RatFunc k) (A := K)
      (algebraMap (RatFunc k) K).injective).2 (RatFunc.transcendental_X (K := k))
  have htC : Transcendental C t := ht.extendScalars C
  let A := IntermediateField.adjoin k ({t} : Set K)
  let B := IntermediateField.adjoin C ({t} : Set K)
  have hAB : A ≤ B.restrictScalars k := IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self C t))
  let : Algebra A B := (IntermediateField.inclusion hAB).toRingHom.toAlgebra
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional A K :=
    FunctionField.FiniteDimensional.adjoin_algebraMap_X (F := k) (K := K)
  have hBK : FiniteDimensional B K := Module.Finite.of_restrictScalars_finite A B K
  exact ⟨t, htC, hBK⟩

/-- Enlarging a perfect base to its full algebraic constant field preserves the curve API. -/
theorem isCurveOver_fullConstants : IsCurveOver (algebraicClosure k K) K := by
  have : PerfectField (algebraicClosure k K) := Algebra.IsAlgebraic.perfectField k
  obtain ⟨t, ht, hfin⟩ := exists_transcendental_finite_fullConstants k K
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht hfin

/-- Every field endomorphism of a global function field which fixes all
normalized place orders is the identity, including on the full constant field. -/
theorem ringHom_eq_id_of_forall_ord_eq
    (σ : K →+* K) (hord : ∀ (v : Place k K) (x : K), v.ord (σ x) = v.ord x) :
    σ = RingHom.id K := by
  obtain ⟨t, ht, _⟩ := exists_transcendental_finite_fullConstants k K
  have hnonconstant : t ∉ (algebraMap (algebraicClosure k K) K).range := by
    rintro ⟨a, ha⟩
    exact ht (ha ▸ isAlgebraic_algebraMap a)
  exact AlgebraicCurve.ringHom_eq_id_of_forall_ord_eq
    (constantsAreBase_fullConstants k K) t hnonconstant σ
    (fun v x => hord (v.forgetConstants (K := k)) x)

end FunctionField
