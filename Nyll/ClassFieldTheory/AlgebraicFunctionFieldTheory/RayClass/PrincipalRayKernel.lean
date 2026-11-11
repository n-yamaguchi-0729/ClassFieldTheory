/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalGenusEqZero
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits

/-!
# The actual principal kernel of the local ray quotient

For a nonzero effective modulus, the diagonal function group injects into the
idele group modulo the actual local congruence groups. Its image is exactly
the kernel of the projection to the ray class group. The injectivity proof
uses the principal-divisor product formula and a positive boundary exponent;
it does not assume a rational boundary point or an exact constant field.

This supplies the function-field side of GCFT. Identifying the ray class
reciprocity target with the reconstructed tame fundamental-group quotient
remains a separate geometric comparison.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel WithZero
open AlgebraicCurve

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private theorem fieldPrincipalUnits_sub_one_lt_one
    {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] [ValuativeRel F]
    (w : Valuation F Γ₀) [w.Compatible] {n : ℕ} (hn : 0 < n)
    (x : Fˣ) (hx : x ∈ LocalFieldTheory.fieldPrincipalUnits F n) :
    w ((x : F) - 1) < 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  have huone := LocalFieldTheory.principalUnits_le_one F hn hu
  have hm : (u : 𝒪[F]) - 1 ∈ 𝓂[F] := by
    have hpow := (LocalFieldTheory.mem_principalUnits_iff F u 1).mp huone
    rwa [pow_one] at hpow
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  have hsmall : ValuativeRel.valuation F (((u : 𝒪[F]) : F) - 1) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one
      (v := ValuativeRel.valuation F)).mp hm
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation F) w).lt_one_iff_lt_one.mp hsmall

/-- Positive higher units have difference from one of valuation less than one
in the original normalized completion valuation. -/
theorem localHigherUnit_sub_one_lt_one (v : Place k K) {n : ℕ} (hn : 0 < n)
    (x : v.adicCompletionˣ) (hx : x ∈ localHigherUnitGroup v n) :
    Valued.v ((x : v.adicCompletion) - 1) < (1 : ℤᵐ⁰) := by
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
  exact fieldPrincipalUnits_sub_one_lt_one
    (Valued.v : Valuation v.adicCompletion ℤᵐ⁰) hn x hx

variable [HasPrincipalDivisors k K] [∀ v : Place k K, v.FiniteResidue]

open AlgebraicCurves.Divisors.Proofs.Divisor_isPrincipal_of_genus_eq_zero.AlgebraicCurve in
/-- A globally integral principal idele congruent to one at a nonempty
boundary is the identity. No residue-degree-one place is required. -/
theorem principalIdele_eq_one_of_mem_congruence
    (m : Modulus k K) (hm : m ≠ 0) (x : Kˣ)
    (hx : IdeleGroup.principalIdele k K x ∈ congruenceSubgroup m) : x = 1 := by
  have hxord (v : Place k K) : v.ord (x : K) = 0 := by
    have hlocal := congruenceSubgroup_le_integralSubgroup m hx v
    have hzero := (IdeleGroup.localOrder_eq_zero_iff v _).mpr hlocal
    exact (IdeleGroup.localOrder_algebraMap v x).symm.trans hzero
  apply Units.ext
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨D, hD, hdegree⟩ := HasPrincipalDivisors.exists_divisor
    (K := k) (F := K) ((x : K) - 1) hne
  have hnonneg : 0 ≤ D := by
    intro v
    rw [hD v]
    exact v.ord_nonneg_of_mem (sub_mem
      (v.mem_toValuationSubring_of_ord_nonneg (hxord v).ge) (one_mem _))
  have hDzero : D = 0 :=
    GenusZeroPrincipal.eq_zero_of_nonneg_of_degree_eq_zero hnonneg hdegree
  have hdiff (v : Place k K) : v.ord ((x : K) - 1) = 0 := by
    rw [← hD v, hDzero]
    rfl
  obtain ⟨v, hv⟩ : ∃ v, m v ≠ 0 := by
    by_contra! hall
    exact hm (Finsupp.ext hall)
  have hsmall := localHigherUnit_sub_one_lt_one v (Nat.pos_of_ne_zero hv)
    ((IdeleGroup.principalIdele k K x) v) (hx v)
  change Valued.v (algebraMap K v.adicCompletion (x : K) - 1) < 1 at hsmall
  rw [← map_one (algebraMap K v.adicCompletion), ← map_sub,
    valued_algebraMap_adicCompletion] at hsmall
  exact hsmall.ne ((v.ord_eq_zero_iff_adicValuation_eq_one hne).mp (hdiff v))

omit [∀ v : Place k K, v.FiniteResidue] in
/-- The restricted product of the actual local groups modulo their specified
unit or principal-unit subgroups. -/
abbrev RayLocalQuotient (m : Modulus k K) := IdeleGroup k K ⧸ congruenceSubgroup m

omit [∀ v : Place k K, v.FiniteResidue] in
/-- The canonical map from the local ray quotient to the ray class group. -/
def localToRayClass (m : Modulus k K) : RayLocalQuotient m →* RayClassGroup m :=
  QuotientGroup.lift (congruenceSubgroup m)
    ((QuotientGroup.mk' (rayClassSubgroup m)).comp IdeleClassGroup.mk) (by
      intro a ha
      exact (QuotientGroup.eq_one_iff _).mpr ⟨a, ha, rfl⟩)

omit [∀ v : Place k K, v.FiniteResidue] in
/-- The diagonal rational-function map into the local ray quotient. -/
def principalToRayLocal (m : Modulus k K) : Kˣ →* RayLocalQuotient m :=
  (QuotientGroup.mk' (congruenceSubgroup m)).comp (IdeleGroup.principalIdele k K)

/-- A nonempty modulus makes the actual diagonal map injective. -/
theorem principalToRayLocal_injective (m : Modulus k K) (hm : m ≠ 0) :
    Function.Injective (principalToRayLocal m) := by
  apply (injective_iff_map_eq_one (principalToRayLocal m)).mpr
  intro x hx
  exact principalIdele_eq_one_of_mem_congruence m hm x
    ((QuotientGroup.eq_one_iff _).mp hx)

omit [∀ v : Place k K, v.FiniteResidue] in
/-- The kernel of the actual ray-class projection consists precisely of
diagonal rational functions; this holds even at zero modulus. -/
theorem localToRayClass_ker (m : Modulus k K) :
    (localToRayClass m).ker = (principalToRayLocal m).range := by
  apply Subgroup.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    constructor
    · intro ha
      obtain ⟨u, hu, hua⟩ := (QuotientGroup.eq_one_iff _).mp ha
      have hprincipal : a / u ∈ IdeleGroup.principalSubgroup k K :=
        QuotientGroup.eq_iff_div_mem.mp hua.symm
      obtain ⟨x, hx⟩ := hprincipal
      refine ⟨x, ?_⟩
      change QuotientGroup.mk' (congruenceSubgroup m)
        (IdeleGroup.principalIdele k K x) = QuotientGroup.mk' (congruenceSubgroup m) a
      have huone : QuotientGroup.mk' (congruenceSubgroup m) u = 1 :=
        (QuotientGroup.eq_one_iff u).mpr hu
      let q := QuotientGroup.mk' (congruenceSubgroup m)
      exact (congrArg q hx).trans ((map_div q a u).trans
        ((congrArg (fun t : RayLocalQuotient m => q a / t) huone).trans (div_one (q a))))
    · rintro ⟨x, hx⟩
      rw [← hx]
      change (QuotientGroup.mk' (rayClassSubgroup m))
        (IdeleClassGroup.mk (IdeleGroup.principalIdele k K x)) = 1
      have hprincipal : IdeleClassGroup.mk (IdeleGroup.principalIdele k K x) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
      rw [hprincipal, map_one]

/-- Nonzero rational functions are canonically the principal kernel of the
actual local ray quotient for every nonempty modulus. -/
def principalRayKernelEquiv (m : Modulus k K) (hm : m ≠ 0) :
    Kˣ ≃* (localToRayClass m).ker :=
  (MonoidHom.ofInjective (principalToRayLocal_injective m hm)).trans
    (MulEquiv.subgroupCongr (localToRayClass_ker m).symm)

/-- The kernel equivalence is the original diagonal map on representatives. -/
theorem principalRayKernelEquiv_apply (m : Modulus k K) (hm : m ≠ 0) (x : Kˣ) :
    (principalRayKernelEquiv m hm x : RayLocalQuotient m) = principalToRayLocal m x := rfl

omit [∀ v : Place k K, v.FiniteResidue] in
/-- The actual local factor retains the full unit quotient prescribed by the
modulus, including the principal units at every boundary place. -/
abbrev RayLocalFactor (m : Modulus k K) (v : Place k K) :=
  v.adicCompletionˣ ⧸ localHigherUnitGroup v (m v)

omit [∀ v : Place k K, v.FiniteResidue] in
/-- Evaluation of the local ray quotient in one actual local factor. -/
def rayLocalComponent (m : Modulus k K) (v : Place k K) :
    RayLocalQuotient m →* RayLocalFactor m v :=
  QuotientGroup.lift (congruenceSubgroup m)
    ((QuotientGroup.mk' (localHigherUnitGroup v (m v))).comp (IdeleGroup.component v))
    (fun _ ha => (QuotientGroup.eq_one_iff _).mpr (ha v))

/-- Triviality of a principal component is precisely the original local
congruence condition, through the original completion embedding. -/
theorem rayLocalComponent_principalRayKernelEquiv_eq_one_iff
    (m : Modulus k K) (hm : m ≠ 0) (v : Place k K) (x : Kˣ) :
    rayLocalComponent m v (principalRayKernelEquiv m hm x) = 1 ↔
      Units.map (algebraMap K v.adicCompletion) x ∈ localHigherUnitGroup v (m v) :=
  QuotientGroup.eq_one_iff _

/-- At a reduced boundary component, the principal-kernel equivalence detects
the full actual group `1 + 𝔪_v`, with no prime-primary replacement. -/
theorem rayLocalComponent_principalRayKernelEquiv_boundary
    (m : Modulus k K) (hm : m ≠ 0) (v : Place k K) (hv : m v = 1) (x : Kˣ) :
    rayLocalComponent m v (principalRayKernelEquiv m hm x) = 1 ↔
      Units.map (algebraMap K v.adicCompletion) x ∈ localHigherUnitGroup v 1 := by
  rw [rayLocalComponent_principalRayKernelEquiv_eq_one_iff, hv]

omit [∀ v : Place k K, v.FiniteResidue] in
/-- Every normalized integer valuation descends through the local ray quotient. -/
def rayLocalOrder (m : Modulus k K) (v : Place k K) :
    RayLocalQuotient m →* Multiplicative ℤ :=
  QuotientGroup.lift (congruenceSubgroup m)
    ((IdeleGroup.localOrder v).comp (IdeleGroup.component v)) (by
      intro a ha
      apply Multiplicative.ext
      exact (IdeleGroup.localOrder_eq_zero_iff v (a v)).mpr
        (congruenceSubgroup_le_integralSubgroup m ha v))

/-- The principal-kernel identification preserves each normalized function-field
valuation, including the boundary places. -/
theorem rayLocalOrder_principalRayKernelEquiv
    (m : Modulus k K) (hm : m ≠ 0) (v : Place k K) (x : Kˣ) :
    (rayLocalOrder m v (principalRayKernelEquiv m hm x)).toAdd = v.ord (x : K) :=
  IdeleGroup.localOrder_algebraMap v x

end FunctionField.RayClass
