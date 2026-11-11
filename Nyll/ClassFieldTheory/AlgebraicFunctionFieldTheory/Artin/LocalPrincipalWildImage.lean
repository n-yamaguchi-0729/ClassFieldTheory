/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayInertia
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup

/-!
# Principal units in the actual finite inertia images

In positive characteristic, Frobenius raises the principal-unit depth.
An open kernel therefore kills a prime-power of every principal unit.
Conversely, an ordinary unit raised to the order of the residue unit
group is a principal unit. That order is prime to the characteristic.
These two computations characterize the original depth-one image inside
the original depth-zero image, without assuming a ramification comparison.
-/

@[expose] public section

noncomputable section

universe u v

open scoped ValuativeRel

namespace LocalFieldTheory

open LocalFieldTheory.IsNonarchimedeanLocalField

section Frobenius

variable (F : Type*) [Field F] [ValuativeRel F]
    (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Frobenius carries depth n principal units into depth pn. -/
theorem fieldPrincipalUnits_pow_prime_mem (n : ℕ) (x : Fˣ)
    (hx : x ∈ fieldPrincipalUnits F n) :
    x ^ p ∈ fieldPrincipalUnits F (n * p) := by
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨u ^ p, ?_, map_pow (integerUnitsToFieldUnits F) u p⟩
  change (↑(u ^ p) : 𝒪[F]) - 1 ∈ (𝓂[F] ^ (n * p) : Ideal 𝒪[F])
  rw [Units.val_pow_eq_pow_val]
  have hpower : (u : 𝒪[F]) ^ p - 1 = ((u : 𝒪[F]) - 1) ^ p := by
    rw [sub_pow_char, one_pow]
  rw [hpower, pow_mul]
  exact Ideal.pow_mem_pow hu p

/-- Iterated Frobenius gives an explicit depth tending to infinity. -/
theorem fieldPrincipalUnits_pow_prime_pow_mem (r : ℕ) (x : Fˣ)
    (hx : x ∈ fieldPrincipalUnits F 1) :
    x ^ (p ^ r) ∈ fieldPrincipalUnits F (p ^ r) := by
  induction r with
  | zero =>
      simpa only [pow_zero, pow_one] using hx
  | succ r ihr =>
      rw [pow_succ, pow_mul]
      exact fieldPrincipalUnits_pow_prime_mem F p (p ^ r) (x ^ (p ^ r)) ihr

end Frobenius

section DiscreteImage

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- A continuous discrete image of the actual first principal units is
a p-group in characteristic p. The open kernel supplies the finite depth. -/
theorem isPGroup_fieldPrincipalUnits_one_map (f : Fˣ →* G) (hf : Continuous f) :
    IsPGroup p ((fieldPrincipalUnits F 1).map f) := by
  have hker : IsOpen (f.ker : Set Fˣ) :=
    (isOpen_discrete ({1} : Set G)).preimage hf
  obtain ⟨n, _, hn⟩ := exists_fieldPrincipalUnits_le_of_isOpen F f.ker hker
  have hbound : n ≤ p ^ n :=
    (Nat.le_mul_of_pos_left n (Fact.out : p.Prime).pos).trans
      (Nat.mul_le_pow (Fact.out : p.Prime).ne_one n)
  have hdepth : fieldPrincipalUnits F (p ^ n) ≤ fieldPrincipalUnits F n :=
    Subgroup.map_mono (principalUnits_antitone F hbound)
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  refine ⟨n, ?_⟩
  apply Subtype.ext
  change y.val ^ (p ^ n) = 1
  rw [← hxy, ← map_pow]
  exact hn (hdepth (fieldPrincipalUnits_pow_prime_pow_mem F p n x hx))

private theorem residueUnitCard_coprime : p.Coprime (Nat.card 𝓀[F]ˣ) := by
  let : Fintype 𝓀[F] := Fintype.ofFinite 𝓀[F]
  have : CharP 𝓀[F] p :=
    CharP.of_ringHom_of_ne_zero (IsLocalRing.residue 𝒪[F]) p (Fact.out : p.Prime).ne_zero
  have hcard : 1 ≤ Nat.card 𝓀[F] := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_iff.mpr Fintype.card_pos
  have hzero : (Nat.card 𝓀[F] : 𝓀[F]) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero 𝓀[F]
  have hnonzero : (Nat.card 𝓀[F]ˣ : 𝓀[F]) ≠ 0 := by
    rw [Nat.card_units, Nat.cast_sub hcard, Nat.cast_one, hzero, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  by_contra hcoprime
  exact hnonzero ((CharP.cast_eq_zero_iff 𝓀[F] p _).mpr
    ((Fact.out : p.Prime).dvd_iff_not_coprime.mpr hcoprime))

/-- The order of the original residue-unit group sends every ordinary
unit into the actual first principal-unit subgroup. -/
theorem fieldPrincipalUnits_zero_pow_residueUnitCard_mem_one (x : Fˣ)
    (hx : x ∈ fieldPrincipalUnits F 0) :
    x ^ Nat.card 𝓀[F]ˣ ∈ fieldPrincipalUnits F 1 := by
  obtain ⟨u, _, rfl⟩ := hx
  refine ⟨u ^ Nat.card 𝓀[F]ˣ, ?_,
    map_pow (integerUnitsToFieldUnits F) u (Nat.card 𝓀[F]ˣ)⟩
  have hpow := congrArg (fun z : 𝓀[F]ˣ => (z : 𝓀[F]))
    (pow_card_eq_one' (x := Units.map (IsLocalRing.residue 𝒪[F]) u))
  rw [Units.val_pow_eq_pow_val] at hpow
  change (IsLocalRing.residue 𝒪[F] (u : 𝒪[F])) ^ Nat.card 𝓀[F]ˣ = 1 at hpow
  apply (mem_principalUnits_iff F _ 1).mpr
  rw [pow_one]
  apply (IsLocalRing.residue_eq_zero_iff _).mp
  rw [map_sub, map_one, Units.val_pow_eq_pow_val, map_pow]
  exact sub_eq_zero.mpr hpow

/-- In every continuous discrete image, the actual depth-one image is
exactly the p-power-order part of the actual ordinary-unit image. -/
theorem mem_fieldPrincipalUnits_one_map_iff (f : Fˣ →* G) (hf : Continuous f) (g : G) :
    g ∈ (fieldPrincipalUnits F 1).map f ↔
      g ∈ (fieldPrincipalUnits F 0).map f ∧ ∃ r : ℕ, g ^ (p ^ r) = 1 := by
  constructor
  · intro hg
    have hle : fieldPrincipalUnits F 1 ≤ fieldPrincipalUnits F 0 :=
      Subgroup.map_mono (principalUnits_antitone F (Nat.zero_le 1))
    refine ⟨Subgroup.map_mono hle hg, ?_⟩
    obtain ⟨r, hr⟩ := isPGroup_fieldPrincipalUnits_one_map F p f hf ⟨g, hg⟩
    exact ⟨r, congrArg Subtype.val hr⟩
  · rintro ⟨hg, r, hr⟩
    have hpower : g ^ Nat.card 𝓀[F]ˣ ∈ (fieldPrincipalUnits F 1).map f := by
      obtain ⟨x, hx, rfl⟩ := hg
      exact ⟨x ^ Nat.card 𝓀[F]ˣ,
        fieldPrincipalUnits_zero_pow_residueUnitCard_mem_one F x hx,
        map_pow f x (Nat.card 𝓀[F]ˣ)⟩
    have hcoprime : (Nat.card 𝓀[F]ˣ).Coprime (orderOf g) :=
      ((residueUnitCard_coprime F p).symm.pow_right r).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one hr)
    obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcoprime
    exact hs ▸ ((fieldPrincipalUnits F 1).map f).pow_mem hpower s

end DiscreteImage

end LocalFieldTheory

namespace FunctionField.RayClass

open AlgebraicCurve LocalClassFieldTheory

attribute [local instance] EtaleFundamentalGroups.Inertia.normalizationCommAlgGaloisAction
attribute [local instance] EtaleFundamentalGroups.Inertia.normalizationInertiaImageAction

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The original completion's first-unit image is intrinsically the
characteristic-primary part of its ordinary-unit image. -/
theorem mem_localHigherUnitGroup_one_map_iff
    (v : Place k K) {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (f : v.adicCompletionˣ →* G) (hf : Continuous f) (g : G) :
    g ∈ (localHigherUnitGroup v 1).map f ↔
      g ∈ (localHigherUnitGroup v 0).map f ∧
        ∃ r : ℕ, g ^ ((ringChar k) ^ r) = 1 := by
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  have hp : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have : CharP v.adicCompletion (ringChar k) :=
    CharP.of_ringHom_of_ne_zero
      ((algebraMap K v.adicCompletion).comp (algebraMap k K)) (ringChar k) hp.out.ne_zero
  exact LocalFieldTheory.mem_fieldPrincipalUnits_one_map_iff
    v.adicCompletion (ringChar k) f hf g

variable [HasPrincipalDivisors k K]

attribute [local instance] placeAmbientAlgebra placeAmbientTower placeStageAmbientTower

/-- In an actual finite abelian Galois restriction, the original local
principal-unit image is exactly the p-power-order part of the original
normalization inertia at the same contracted prime. -/
theorem mem_placeArtinUnitImage_one_restriction_iff
    (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (g : Gal(E/K)) :
    g ∈ (placeArtinUnitImage v 1).map (absoluteAbelianRestriction K E).toMonoidHom ↔
      g ∈ (placeAbsolutePrimeAt v Q E).asIdeal.inertia Gal(E/K) ∧
        ∃ r : ℕ, g ^ ((ringChar k) ^ r) = 1 := by
  let f : v.adicCompletionˣ →* Gal(E/K) :=
    (absoluteAbelianRestriction K E).toMonoidHom.comp (placeAbsoluteArtin v)
  have hf : Continuous f := (absoluteAbelianRestriction K E).continuous_toFun.comp
    ((absoluteArtin k K).continuous_toFun.comp
      (QuotientGroup.continuous_mk.comp (IdeleGroup.continuous_placeIdele v)))
  have hmap (n : ℕ) :
      (placeArtinUnitImage v n).map (absoluteAbelianRestriction K E).toMonoidHom =
        (localHigherUnitGroup v n).map f := by
    rw [placeArtinUnitImage, Subgroup.map_map]
    rfl
  have hzero : (localHigherUnitGroup v 0).map f =
      (placeAbsolutePrimeAt v Q E).asIdeal.inertia Gal(E/K) := by
    rw [← hmap 0]
    exact placeArtinUnitImage_zero_restriction v Q E
  rw [hmap 1, mem_localHigherUnitGroup_one_map_iff v f hf g, hzero]

end FunctionField.RayClass
