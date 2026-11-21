/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.CyclicSplittingLocalOrders
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.CyclicSplittingStage
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InvariantSum
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
public import Nyll.ProCGroups.Abelian.AvoidFiniteFibers
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Nat.Factorization.Basic

/-! # A common cyclic extension for prescribed finite local orders -/

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity
open scoped NumberField Cyclotomic DirectSum

namespace ClassFieldTheory.Brauer

private def characterEvaluation {G A : Type*} [Group G] [CommGroup A] (g : G) :
    (G →* A) →* A where
  toFun χ := χ g
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem orderOf_dvd_card_characterEvaluation_range
    {G F : Type*} [CommGroup G] [Finite G] [Field F]
    (n : ℕ+) (hμ : (primitiveRoots (n : ℕ) F).Nonempty)
    (hN : ∀ g : G, g ^ (n : ℕ) = 1) (g : G) :
    orderOf g ∣ Nat.card (characterEvaluation (A := nthRootsSubgroup F n) g).range := by
  let ev := characterEvaluation (A := nthRootsSubgroup F n) g
  apply orderOf_dvd_of_pow_eq_one
  by_contra hg
  obtain ⟨χ, hχ⟩ := exists_nthRoots_character_apply_ne_one n hμ hN hg
  apply hχ
  rw [map_pow]
  exact congrArg Subtype.val (pow_card_eq_one' (x := ev.rangeRestrict χ))

open IdeleGroup in
/-- A finite family of prime-power divisibility requirements and ramification at
all real places are realized in one actual cyclic extension. -/
theorem exists_cyclicStage_finitePlace_primePower_dvd_and_ramifies_real
    (K : Type*) [Field K] [NumberField K] {ι : Type*} [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 K)) (p e : ι → ℕ) (hp : ∀ i, (p i).Prime) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), IsCyclic Gal(E/K) ∧
      (∀ i, p i ^ (e i + 1) ∣
        Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) (v i))
          (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) (v i))) ∧
      ∀ v : InfinitePlace K, v.IsReal → (chosenInfinitePlaceAbove (L := E) v).IsRamified K := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let r := Fintype.card ι
  let s (i : ι) := p i ^ (e i + (r + 1))
  have hs (i : ι) : 0 < s i := pow_pos (hp i).pos _
  choose m a ha using fun i =>
    exists_cyclotomicIdeleClassCharacter_local_order K (v i) (s i) (hs i)
  let _ (i : ι) : NeZero (m i : ℕ) := ⟨(m i).pos.ne'⟩
  let B (i : ι) := (ZMod (m i : ℕ))ˣ
  let realOrder := rationalComplexificationCyclotomicOrder
  let _ : NeZero (realOrder : ℕ) := ⟨realOrder.pos.ne'⟩
  let RealFactor := (ZMod (realOrder : ℕ))ˣ
  let H := (∀ i : ι, B i) × RealFactor
  let Φfin : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* (∀ i : ι, B i) :=
    ⟨{ toFun := fun c i => cyclotomicIdeleClassCharacter K (m i) c
       map_one' := funext fun i => map_one (cyclotomicIdeleClassCharacter K (m i))
       map_mul' := fun c d => funext fun i => map_mul (cyclotomicIdeleClassCharacter K (m i)) c d },
      continuous_pi fun i => (cyclotomicIdeleClassCharacter K (m i)).continuous⟩
  let realCharacter := cyclotomicIdeleClassCharacter K realOrder
  let Φ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* H :=
    ⟨Φfin.toMonoidHom.prod realCharacter.toMonoidHom,
      Φfin.continuous.prodMk realCharacter.continuous⟩
  let x (i : ι) := Φ (IdeleGroup.finitePlaceIdeleClass (v i) (a i))
  have hd (i : ι) : s i ∣ orderOf (x i) := by
    rw [← ha i]
    exact orderOf_map_dvd ((Pi.evalMonoidHom B i).comp (MonoidHom.fst _ RealFactor)) (x i)
  let b (i : ι) := a i ^ (orderOf (x i) / s i)
  let y (i : ι) := Φ (IdeleGroup.finitePlaceIdeleClass (v i) (b i))
  have hy (i : ι) : orderOf (y i) = s i := by
    change orderOf (Φ (IdeleGroup.finitePlaceIdeleClass (v i)
      (a i ^ (orderOf (x i) / s i)))) = s i
    rw [map_pow, map_pow]
    exact orderOf_pow_orderOf_div (orderOf_pos (x i)).ne' (hd i)
  let n : ℕ+ := ⟨Nat.card H, Nat.card_pos⟩
  let : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  let A := nthRootsSubgroup rationalCyclotomicField (n : ℕ)
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let er := nthRootsSubgroupEquivRootsOfUnity rationalCyclotomicField (n : ℕ)
  let : IsCyclic A := isCyclic_of_injective er.toMonoidHom er.injective
  let : Finite (H →* A) :=
    Finite.of_injective (fun χ : H →* A => (χ : H → A)) DFunLike.coe_injective
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    (S := (Set.univ : Set ℕ)) ℚ rationalCyclotomicField (Set.mem_univ (n : ℕ)) n.ne_zero
  have hμ : (primitiveRoots (n : ℕ) rationalCyclotomicField).Nonempty :=
    ⟨ζ, (mem_primitiveRoots n.pos).mpr hζ⟩
  let signValue : RealFactor := rationalCyclotomicIdeleClassCharacter realOrder
    (IdeleGroup.infinitePlaceIdeleClass Rat.infinitePlace (-1 : Rat.infinitePlace.Completionˣ))
  have hsign : signValue ≠ 1 :=
    rationalCyclotomicIdeleClassCharacter_complexification_neg_one_ne_one
  have hRealPower (b : RealFactor) : b ^ (n : ℕ) = 1 := by
    let pr : H →* RealFactor := MonoidHom.snd _ _
    have h := congrArg pr (pow_card_eq_one' (x := ((1, b) : H)))
    rwa [map_pow, map_one] at h
  obtain ⟨κ, hκ⟩ := exists_nthRoots_character_apply_ne_one n hμ hRealPower hsign
  let realSignCharacter : H →* A := κ.comp (MonoidHom.snd _ RealFactor)
  let t (i : ι) := y i ^ (p i ^ e i)
  let test (i : ι) := characterEvaluation (A := A) (t i ^ 2)
  have htest (i : ι) : Fintype.card ι < Nat.card (test i).range := by
    have ho : orderOf (t i) = p i ^ (r + 1) := by
      have hdiv : p i ^ e i ∣ orderOf (y i) := by
        rw [hy, show s i = p i ^ (e i + (r + 1)) from rfl, pow_add]
        exact dvd_mul_right _ _
      change orderOf (y i ^ (p i ^ e i)) = _
      rw [orderOf_pow_of_dvd (pow_pos (hp i).pos _).ne' hdiv, hy,
        show s i = p i ^ (e i + (r + 1)) from rfl, pow_add]
      exact Nat.mul_div_cancel_left _ (pow_pos (hp i).pos _)
    have hsquare : p i ^ r ∣ orderOf (t i ^ 2) := by
      by_cases htwo : p i = 2
      · have hdiv : 2 ∣ orderOf (t i) := by
          rw [ho, htwo, pow_succ']
          exact dvd_mul_right _ _
        rw [orderOf_pow_of_dvd (by decide : (2 : ℕ) ≠ 0) hdiv, ho, htwo, pow_succ',
          Nat.mul_div_cancel_left _ (by decide : 0 < (2 : ℕ))]
      · have hcop : (p i).Coprime 2 := (hp i).coprime_iff_not_dvd.mpr fun h =>
          htwo (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left (hp i).ne_one)
        rw [orderOf_pow' _ (by decide : (2 : ℕ) ≠ 0), ho,
          (hcop.pow_left (r + 1)).gcd_eq_one, Nat.div_one]
        exact pow_dvd_pow _ (Nat.le_succ r)
    have hdiv := orderOf_dvd_card_characterEvaluation_range n hμ
      (fun g : H => pow_card_eq_one' (x := g)) (t i ^ 2)
    exact (Nat.lt_pow_self (n := r) (hp i).one_lt).trans_le
      (Nat.le_of_dvd Nat.card_pos (hsquare.trans hdiv))
  obtain ⟨χ, hχ⟩ := ProCGroups.Abelian.exists_forall_apply_ne_of_card_lt_card_range
    test (fun i => (realSignCharacter (t i))⁻¹) htest
  let ψ := realSignCharacter * χ ^ 2
  let θ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A :=
    ⟨ψ.comp Φ.toMonoidHom, (continuous_of_discreteTopology (f := ψ)).comp Φ.continuous⟩
  obtain ⟨E, hab, hcyc, ρ, _, hρ, hlocal⟩ := exists_cyclicStage_of_ideleClassCharacter K θ
  refine ⟨E, hcyc, fun i => ?_, fun w hw => ?_⟩
  · apply dvd_trans _ (hlocal (v i) (b i))
    change p i ^ (e i + 1) ∣ orderOf (ψ (y i))
    have hdiv := orderOf_map_dvd ψ (y i)
    rw [hy] at hdiv
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (hp i)).mp hdiv
    have hle : e i + 1 ≤ k := by
      by_contra! hl
      have hdvd : orderOf (ψ (y i)) ∣ p i ^ e i := by
        rw [hk]
        exact pow_dvd_pow _ (by omega)
      have ht : ψ (t i) = 1 := by
        change ψ (y i ^ (p i ^ e i)) = 1
        rw [map_pow]
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      apply hχ i
      change realSignCharacter (t i) * χ (t i) ^ 2 = 1 at ht
      change χ (t i ^ 2) = (realSignCharacter (t i))⁻¹
      rw [map_pow]
      exact eq_inv_of_mul_eq_one_right ht
    rw [hk]
    exact pow_dvd_pow _ hle
  · let _ : NumberField E := NumberField.of_module_finite K E
    let _ : IsAbelianGalois K E := hab
    let c := IdeleGroup.infinitePlaceIdeleClass w (-1 : w.Completionˣ)
    have hc : c ^ 2 = 1 := by
      change (IdeleGroup.infinitePlaceIdeleClass w (-1 : w.Completionˣ)) ^ 2 = 1
      rw [← map_pow, neg_one_sq, map_one]
    have hθ : θ c ≠ 1 := by
      change κ (realCharacter c) * χ (Φ c) ^ 2 ≠ 1
      have hχsq : χ (Φ c) ^ 2 = 1 := by rw [← map_pow, ← map_pow, hc, map_one, map_one]
      rw [hχsq, mul_one]
      change κ (cyclotomicIdeleClassCharacter K realOrder
        (IdeleGroup.infinitePlaceIdeleClass w (-1 : w.Completionˣ))) ≠ 1
      rw [cyclotomicIdeleClassCharacter_real_neg_one K realOrder w hw]
      exact hκ
    intro hunramified
    let W := chosenInfinitePlaceAbove (L := E) w
    have hnorm :=
      ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isUnramified
        (K := K) (L := E) W hunramified (-1 : (infinitePlaceBelow (K := K) W).Completionˣ)
    have hBelow : infinitePlaceBelow (K := K) W = w := chosenInfinitePlaceAbove_comap (L := E) w
    rw [IdeleGroup.infinitePlaceBaseUnitExtension_neg_one, hBelow] at hnorm
    have hmem : c ∈ (ideleClassNorm K E).range := ⟨_, hnorm⟩
    have hartin : arithmeticGlobalNormResidueMonoidHom K E c = 1 := by
      rw [← arithmeticGlobalNormResidueMonoidHom_ker] at hmem
      exact MonoidHom.mem_ker.mp hmem
    apply hθ
    rw [← hρ, hartin, map_one]

/-- The finite local divisibilities of the common cyclic extension. -/
theorem exists_cyclicStage_finitePlace_primePower_dvd
    (K : Type*) [Field K] [NumberField K] {ι : Type*} [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 K)) (p e : ι → ℕ) (hp : ∀ i, (p i).Prime) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), IsCyclic Gal(E/K) ∧
      ∀ i, p i ^ (e i + 1) ∣
        Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) (v i))
          (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) (v i)) := by
  obtain ⟨E, hcyc, hfin, _⟩ :=
    exists_cyclicStage_finitePlace_primePower_dvd_and_ramifies_real K v p e hp
  exact ⟨E, hcyc, hfin⟩

/-- Any finite list of positive local degree divisors is realized by a single cyclic
extension ramified at all real places. -/
theorem exists_cyclicStage_finitePlace_degree_dvd_and_ramifies_real
    (K : Type*) [Field K] [NumberField K] {ι : Type*} [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 K)) (d : ι → ℕ+) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), IsCyclic Gal(E/K) ∧
      (∀ i, (d i : ℕ) ∣ Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) (v i))
        (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) (v i))) ∧
      ∀ v : InfinitePlace K, v.IsReal → (chosenInfinitePlaceAbove (L := E) v).IsRamified K := by
  classical
  let J := Σ i : ι, ↥((d i : ℕ).primeFactors)
  let w (j : J) := v j.1
  let p (j : J) := (j.2 : ℕ)
  let e (j : J) := (d j.1 : ℕ).factorization (p j) - 1
  obtain ⟨E, hcyc, hfin, hreal⟩ :=
    exists_cyclicStage_finitePlace_primePower_dvd_and_ramifies_real K w p e
      (fun j => Nat.prime_of_mem_primeFactors j.2.2)
  refine ⟨E, hcyc, fun i => ?_, hreal⟩
  let N := Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) (v i))
    (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) (v i))
  have hN : 0 < N := Module.finrank_pos
  change (d i : ℕ) ∣ N
  apply (Nat.factorization_le_iff_dvd (d i).ne_zero hN.ne').mp
  intro q
  by_cases hq : q ∈ (d i : ℕ).primeFactors
  · let j : J := ⟨i, ⟨q, hq⟩⟩
    have hp := Nat.prime_of_mem_primeFactors hq
    have hpos := hp.factorization_pos_of_dvd (d i).ne_zero (Nat.mem_primeFactors.mp hq).2.1
    have hdiv := hfin j
    change q ^ ((d i : ℕ).factorization q - 1 + 1) ∣ N at hdiv
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)] at hdiv
    exact (hp.pow_dvd_iff_le_factorization hN.ne').mp hdiv
  · have hz : (d i : ℕ).factorization q = 0 := Finsupp.notMem_support_iff.mp (by
      rwa [Nat.support_factorization])
    rw [hz]
    exact Nat.zero_le _

private theorem addOrderOf_rationalCircle_pos (z : AddCircle (1 : ℚ)) : 0 < addOrderOf z := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) z
  apply IsOfFinAddOrder.addOrderOf_pos
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨q.den, q.den_pos, ?_⟩
  change q.den • (q : AddCircle (1 : ℚ)) = 0
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, RayClass.rational_den_mul_self_eq_num]
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨q.num, by rw [zsmul_eq_mul, mul_one]⟩

/-- The finite orders in a tuple of local Brauer classes divide the completed degrees
of one cyclic splitting stage. Every real place ramifies in the same extension. -/
theorem exists_cyclicStage_for_localBrauerTuple
    (K : Type*) [Field K] [NumberField K]
    (x : ⨁ v : Place K, Br (placeCompletion K v)) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), IsCyclic Gal(E/K) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), addOrderOf (x (Sum.inl v)) ∣
        Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
          (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v)) ∧
      ∀ v : InfinitePlace K, v.IsReal → (chosenInfinitePlaceAbove (L := E) v).IsRamified K := by
  classical
  let S := x.support.preimage (Sum.inl : HeightOneSpectrum (𝓞 K) → Place K) Sum.inl_injective.injOn
  let d (v : ↥S) : ℕ+ := ⟨addOrderOf (x (Sum.inl v.1)), by
    let e := finitePlaceBrauerInvariantEquiv K v.1
    rw [← addOrderOf_injective e.toAddMonoidHom e.injective]
    exact addOrderOf_rationalCircle_pos (e (x (Sum.inl v.1)))⟩
  obtain ⟨E, hcyc, hfin, hreal⟩ :=
    exists_cyclicStage_finitePlace_degree_dvd_and_ramifies_real K (fun v : ↥S => v.1) d
  refine ⟨E, hcyc, fun v => ?_, hreal⟩
  by_cases hv : v ∈ S
  · exact hfin ⟨v, hv⟩
  · have hvs : Sum.inl v ∉ x.support := fun hm => hv (Finset.mem_preimage.mpr hm)
    rw [DFinsupp.notMem_support_iff.mp hvs, addOrderOf_zero]
    exact one_dvd _

end ClassFieldTheory.Brauer
