/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePerfectness
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalCohomologicalDimension
public import Nyll.GaloisCohomology.Topology.ContinuousCupCorestriction
public import Nyll.GaloisCohomology.Topology.ContinuousEulerMultiplicity
public import Nyll.GaloisCohomology.Topology.ContinuousShapiro
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtensionContinuous

/-! # Euler characteristic for local coefficients with prime-power action image -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ContinuousCohomology ContRepresentation TopRep LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open ClassFieldTower.Cohomology

noncomputable section

namespace ContinuousCohomology

universe u

/-- The Euler ratio of actual open-subgroup coinduction is the Euler ratio on the subgroup. -/
theorem lowDegreeEulerCharacteristic_openCoinduced {Γ : Type u} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (U : OpenSubgroup Γ) (A : TopRep.{u} ℤ ↥U) :
    let : IsTopologicalGroup ↥U :=
      Topology.IsInducing.subtypeVal.isTopologicalGroup (U : Subgroup Γ).subtype
    lowDegreeEulerCharacteristic ((continuousModuleComplexFunctor Γ).obj (openCoinduced U A)) =
      lowDegreeEulerCharacteristic ((continuousModuleComplexFunctor ↥U).obj A) := by
  intro subgroupTopology
  let B := openCoinduced U A
  let X := (continuousModuleComplexFunctor Γ).obj B
  let Y := (continuousModuleComplexFunctor ↥U).obj A
  have h (i : ℕ) (hi : i < 3) : Nat.card (X.homology i) = Nat.card (Y.homology i) := by
    let e := continuousModuleHomologyIso Γ B i
    let f := continuousModuleHomologyIso ↥U A i
    let E := Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom)
    exact Nat.card_congr (E.trans
      ((openShapiroEquiv U A i hi).toEquiv.trans
        (Equiv.ofBijective f.inv (ConcreteCategory.bijective_of_isIso f.inv))))
  change lowDegreeEulerCharacteristic X = lowDegreeEulerCharacteristic Y
  rw [lowDegreeEulerCharacteristic, lowDegreeEulerCharacteristic,
    h 0 (by decide), h 1 (by decide), h 2 (by decide)]

end ContinuousCohomology

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact
  localTateTrivialCoefficient_discrete

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

local notation "G" => Gal(SeparableClosure K/K)
local notation "H" => _root_.continuousCohomology (k := ℤ)
local notation "C" => continuousModuleComplexFunctor G

private def trivialPrimeHomologyEquiv (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (i : ℕ) :
    (((C).obj (trivialIntegralZModPLifted p G)).homology i) ≃ H i (separableMuTopRep K p) := by
  let M := separableMuTopRep K p
  let F := C ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) i
  let E := F.mapIso (primitiveKummerTrivialIso K p hζ) ≪≫ continuousModuleHomologyIso G M i
  exact Equiv.ofBijective E.hom (ConcreteCategory.bijective_of_isIso E.hom)

private theorem finite_trivialPrimeHomology_of_primitive (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : (p : K) ≠ 0) (i : ℕ) (hi : i < 3) :
    Finite (((C).obj (trivialIntegralZModPLifted p G)).homology i) := by
  let n : ℕ+ := ⟨p, (Fact.out : p.Prime).pos⟩
  let e := trivialPrimeHomologyEquiv K p hζ i
  obtain ⟨h0, h1, h2⟩ := finite_localKummerH012 K n hp
  let : Finite (H i (separableMuTopRep K p)) := by
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
  exact Finite.of_injective e e.injective

private theorem natCard_linearDual {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Finite V] : Nat.card (V →ₗ[k] k) = Nat.card V := by
  let : Module.Finite k V := Module.Finite.of_finite
  let b := Module.finBasis k V
  exact Nat.card_congr (b.dualBasis.equivFun.toEquiv.trans b.equivFun.symm.toEquiv)

private theorem natCard_addHom_zmod_prime (p : ℕ) [Fact p.Prime]
    (V : Type u) [AddCommGroup V] [Finite V] (hV : ∀ v : V, p • v = 0) :
    Nat.card (V →+ ZMod p) = Nat.card V := by
  let scalar : Module (ZMod p) V := AddCommGroup.zmodModule hV
  let : Module (ZMod p) V := scalar
  let e : (V →+ ZMod p) ≃ (V →ₗ[ZMod p] ZMod p) :=
    (AddMonoidHom.toZModLinearMapEquiv p).toEquiv
  exact (Nat.card_congr e).trans (@natCard_linearDual (ZMod p) V _ _ scalar _)

section MixedEuler

variable [CharZero K]

/-- The rational normalized local absolute value of a positive coefficient order. -/
def localCoefficientOrderNorm (m : ℕ) : ℚ :=
  let v := localIntegerValuation K
  let F := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  (F.residueCharacteristic : ℚ)⁻¹ ^ (d * padicValNat F.residueCharacteristic m)

theorem localCoefficientOrderNorm_one : localCoefficientOrderNorm K 1 = 1 := by
  unfold localCoefficientOrderNorm
  simp only [Nat.padicValNat_def, multiplicity_one_right, mul_zero, pow_zero]

theorem localCoefficientOrderNorm_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    localCoefficientOrderNorm K (m * n) = localCoefficientOrderNorm K m *
      localCoefficientOrderNorm K n := by
  let v := localIntegerValuation K
  let F := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  let q := F.residueCharacteristic
  let d := Module.finrank ℚ_[q] K
  let : Fact q.Prime := ⟨F.residueCharacteristic_prime⟩
  change (q : ℚ)⁻¹ ^ (d * padicValNat q (m * n)) =
    (q : ℚ)⁻¹ ^ (d * padicValNat q m) * (q : ℚ)⁻¹ ^ (d * padicValNat q n)
  simp only [Nat.padicValNat_def]
  rw [Nat.multiplicity_mul hm.ne' hn.ne', mul_add, pow_add]

private def padicPrimeCongr {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) :
    ℚ_[p] ≃+* ℚ_[q] := by
  subst q
  exact RingEquiv.refl _

private theorem padicPrimeCongr_continuous {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) :
    Continuous (padicPrimeCongr h) := by
  subst q
  exact continuous_id

private theorem finrank_padicPrimeCongr (L : Type u) [Field L] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] [coefL : Algebra ℚ_[q] L] (h : p = q) :
    let a := ((algebraMap ℚ_[q] L).comp (padicPrimeCongr h).toRingHom).toAlgebra
    @Module.finrank ℚ_[p] L _ _ a.toModule = Module.finrank ℚ_[q] L := by
  subst q
  let a := ((algebraMap ℚ_[p] L).comp (RingHom.id ℚ_[p])).toAlgebra
  change @Module.finrank ℚ_[p] L _ _ a.toModule = @Module.finrank ℚ_[p] L _ _ coefL.toModule
  have ha : a = coefL := Algebra.algebra_ext a coefL fun _ => rfl
  exact congrArg (fun b : Algebra ℚ_[p] L => @Module.finrank ℚ_[p] L _ _ b.toModule) ha

/-- The normalized Euler order norm scales by the degree of a finite valued extension.
The canonical p-adic scalar maps agree on dense rational elements. -/
theorem localCoefficientOrderNorm_finiteExtension (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (m : ℕ) :
    let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    localCoefficientOrderNorm L m = localCoefficientOrderNorm K m ^ Module.finrank K L := by
  intro charL
  let vK := localIntegerValuation K
  let vL := localIntegerValuation L
  let FK := LocalField.ofWithZeroValuation vK
  let FL := LocalField.ofWithZeroValuation vL
  let : LocalField.MixedWithZeroValuationContext vK := LocalField.mixedWithZeroValuationContext vK
  let : LocalField.MixedWithZeroValuationContext vL := LocalField.mixedWithZeroValuationContext vL
  let p := FK.residueCharacteristic
  let q := FL.residueCharacteristic
  let : Fact p.Prime := ⟨FK.residueCharacteristic_prime⟩
  let : Fact q.Prime := ⟨FL.residueCharacteristic_prime⟩
  have hVal : vK.HasExtension vL := localIntegerValuation_hasExtension K L
  let : vK.HasExtension vL := hVal
  let : FK.toDVF.valuation.HasExtension FL.toDVF.valuation := hVal
  have hpq : p = q :=
    (ValuationTheory.DiscreteValuationField.ValuedExtension.residueField_ringChar_eq_of_hasExtension
      FK.toCompleteDVF.toDVF FL.toCompleteDVF.toDVF).symm
  let e := padicPrimeCongr hpq
  let φ := (algebraMap ℚ_[q] L).comp e.toRingHom
  have hdim := finrank_padicPrimeCongr L hpq
  let dK := Module.finrank ℚ_[p] K
  let dL := Module.finrank ℚ_[q] L
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' vK
  let : Valued L (WithZero (Multiplicative ℤ)) := Valued.mk' vL
  let : TopologicalSpace K := (Valued.mk' vK).toUniformSpace.toTopologicalSpace
  let : TopologicalSpace L := (Valued.mk' vL).toUniformSpace.toTopologicalSpace
  have hK : Continuous (algebraMap ℚ_[p] K) :=
    LocalField.continuous_qpadicNumbersAlgebra_ofWithZeroValuation vK
  have hL : Continuous (algebraMap ℚ_[q] L) :=
    LocalField.continuous_qpadicNumbersAlgebra_ofWithZeroValuation vL
  have hKL : Continuous (algebraMap K L) :=
    ValuationTheory.DiscreteValuationField.Valuation.continuous_algebraMap_of_hasExtension vK vL
  have hclosed : IsClosed {x : ℚ_[p] | φ x = algebraMap K L (algebraMap ℚ_[p] K x)} :=
    isClosed_eq (hL.comp (padicPrimeCongr_continuous hpq)) (hKL.comp hK)
  have hmap (x : ℚ_[p]) : φ x = algebraMap K L (algebraMap ℚ_[p] K x) := by
    refine (Padic.denseRange_ratCast p).induction_on x hclosed ?_
    intro a
    simp only [map_ratCast]
  let : Algebra ℚ_[p] L := φ.toAlgebra
  let : IsScalarTower ℚ_[p] K L := IsScalarTower.of_algebraMap_eq hmap
  have hdegrees : dK * Module.finrank K L = dL :=
    (Module.finrank_mul_finrank ℚ_[p] K L).trans hdim
  change (q : ℚ)⁻¹ ^ (dL * padicValNat q m) =
    ((p : ℚ)⁻¹ ^ (dK * padicValNat p m)) ^ Module.finrank K L
  rw [← hdegrees, ← hpq, ← pow_mul]
  exact congrArg (fun a : ℕ => (p : ℚ)⁻¹ ^ a) (mul_right_comm _ _ _)

/-- The normalized coefficient order of coinduction is the original order
norm, raised to the open subgroup index. -/
theorem localCoefficientOrderNorm_openCoinduced (U : OpenSubgroup G)
    (A : TopRep.{u} ℤ ↥U) [Finite A]
    (hA : Continuous (fun ga : ↥U × A => A.ρ ga.1 ga.2)) :
    localCoefficientOrderNorm K (Nat.card (openCoinduced U A)) =
      localCoefficientOrderNorm K (Nat.card A) ^ U.toSubgroup.index := by
  rw [natCard_openCoinduced U A hA]
  have hpow (n : ℕ) : localCoefficientOrderNorm K (Nat.card A ^ n) =
      localCoefficientOrderNorm K (Nat.card A) ^ n := by
    induction n with
    | zero => rw [pow_zero, pow_zero, localCoefficientOrderNorm_one]
    | succ n ih =>
      rw [pow_succ, pow_succ,
        localCoefficientOrderNorm_mul K _ _ (pow_pos Nat.card_pos _) Nat.card_pos, ih]
  exact hpow U.toSubgroup.index

/-- The trivial prime coefficient has the Euler ratio without choosing a root in the base. -/
theorem localEulerCoefficient_trivial (p : ℕ) [Fact p.Prime] :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (trivialIntegralZModPLifted p G) := by
  let hp := (Fact.out : p.Prime)
  let n : ℕ+ := ⟨p, hp.pos⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let T := trivialIntegralZModPLifted p G
  let M := separableMuTopRep K p
  let D := discreteLinearDual T M
  let : Finite T := inferInstanceAs (Finite (ULift.{u} (ZMod p)))
  let c (i : ℕ) := Nat.card (H i T)
  let k (i : ℕ) := Nat.card (H i M)
  have hn : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hT (x : T) : p • x = 0 := by
    apply ULift.ext
    exact ZModModule.char_nsmul_eq_zero p (show ULift.{u} (ZMod p) from x).down
  have hD (f : D) : p • f = 0 := by
    apply LinearMap.ext
    intro x
    exact separableMuTopRep_nsmul_eq_zero K p (discreteLinearDualMap T M f x)
  let e := primeCharacterDualIso K p
  let F (i : ℕ) := homogeneousContinuousCochainsFunctorOver ℤ G ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{u} ℤ) (ComplexShape.up ℕ) i
  let eH (i : ℕ) : H i D ≃ H i M :=
    let f := (F i).mapIso e
    Equiv.ofBijective f.hom (ConcreteCategory.bijective_of_isIso f.hom)
  obtain ⟨hk0, hk1, _⟩ := finite_localKummerH012 K n hn
  let : Finite (H 0 M) := hk0
  let : Finite (H 1 M) := hk1
  let : Finite (H 0 D) := Finite.of_injective (eH 0) (eH 0).injective
  let : Finite (H 1 D) := Finite.of_injective (eH 1) (eH 1).injective
  have hP := localTatePairingAdjoints_bijective K n T hn continuous_snd hT
  let e₁ := Equiv.ofBijective (localTatePairingOneAdjoint K n T hn) hP.2.1
  let e₂ := Equiv.ofBijective (localTatePairingTwoAdjoint K n T hn) hP.2.2
  let eInv : T.invariants ≃ ULift.{u} (ZMod p) :=
    ⟨Subtype.val, fun t => ⟨t, fun _ => rfl⟩, fun _ => Subtype.ext rfl, fun _ => rfl⟩
  let e₀ := (Equiv.ofBijective (zeroIso T).hom
    (ConcreteCategory.bijective_of_isIso (zeroIso T).hom)).trans eInv
  have hcardT : Nat.card T = p := (Nat.card_congr Equiv.ulift).trans (Nat.card_zmod p)
  have hc0 : c 0 = p := (Nat.card_congr e₀).trans hcardT
  have hc1 : c 1 = k 1 := (Nat.card_congr e₁).trans
    ((natCard_addHom_zmod_prime p (H 1 D)
      (nsmul_continuousCohomology_eq_zero_of_coefficients D p hD 1)).trans (Nat.card_congr (eH 1)))
  have hc2 : c 2 = k 0 := (Nat.card_congr e₂).trans
    ((natCard_addHom_zmod_prime p (H 0 D)
      (nsmul_continuousCohomology_eq_zero_of_coefficients D p hD 0)).trans (Nat.card_congr (eH 0)))
  let : Finite (H 0 T) := Finite.of_injective e₀ e₀.injective
  let f₁ (x : H 1 T) (y : H 1 D) : ZMod p := e₁ x y
  let f₂ (x : H 2 T) (y : H 0 D) : ZMod p := e₂ x y
  let : Finite (H 1 T) := Finite.of_injective f₁
    (fun _ _ he => e₁.injective (AddMonoidHom.ext fun y => congrFun he y))
  let : Finite (H 2 T) := Finite.of_injective f₂
    (fun _ _ he => e₂.injective (AddMonoidHom.ext fun y => congrFun he y))
  have hFin (i : ℕ) (hi : i < 3) : Finite (H i T) := by
    interval_cases i <;> infer_instance
  let eC (i : ℕ) := continuousModuleHomologyIso G T i
  have hc (i : ℕ) : Nat.card (((C).obj T).homology i) = c i :=
    Nat.card_congr (Equiv.ofBijective (eC i).hom (ConcreteCategory.bijective_of_isIso (eC i).hom))
  refine ⟨?_, ?_⟩
  · intro i hi
    let : Finite (H i T) := hFin i hi
    exact Finite.of_injective (eC i).hom (ConcreteCategory.bijective_of_isIso (eC i).hom).1
  let v := localIntegerValuation K
  let R := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  let q := R.residueCharacteristic
  let d := Module.finrank ℚ_[q] K
  let b := d * padicValNat q p
  have hprodK : k 1 = k 2 * (k 0 * q ^ b) := localKummerEuler_mixed K n
  have hk2 : k 2 = p := card_localKummerH2 K n hn
  have hprod : c 1 = c 0 * (c 2 * q ^ b) := by
    rw [hc1, hc0, hc2, ← hk2]
    exact hprodK
  have hprodQ : (c 1 : ℚ) = (c 0 : ℚ) * ((c 2 : ℚ) * (q : ℚ) ^ b) := by
    exact_mod_cast hprod
  have h1Q : (c 1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hb : (q : ℚ) ^ b ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr R.residueCharacteristic_prime.ne_zero)
  rw [lowDegreeEulerCharacteristic, hc 0, hc 1, hc 2, hcardT]
  change (c 0 : ℚ) * (c 2 : ℚ) / (c 1 : ℚ) = (q : ℚ)⁻¹ ^ b
  rw [inv_pow, div_eq_iff h1Q, hprodQ]
  rw [show (c 0 : ℚ) * ((c 2 : ℚ) * (q : ℚ) ^ b) =
    (q : ℚ) ^ b * ((c 0 : ℚ) * (c 2 : ℚ)) by ac_rfl]
  rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]

/-- The local Euler formula for finite prime-annihilated coefficients with p-group action image. -/
theorem localEulerCoefficient_of_pGroup_image (p : ℕ) [Fact p.Prime]
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0)
    (hρ : let _ : Module ℤ A := A.hV2; IsPGroup p A.ρ.toRepresentation.asGroupHom.range) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K) A :=
  hasLowDegreeEulerCharacteristic_of_pGroup_image G (localCoefficientOrderNorm K) p
    (localCoefficientOrderNorm_one K) (localCoefficientOrderNorm_mul K)
    (finiteLocalIntegralH3_isZero K)
    (localEulerCoefficient_trivial K p) A hA hp hρ

/-- The Euler ratio gives the cardinal formula on the original continuous cohomology. -/
theorem card_localH1_of_eulerCharacteristic (A : TopRep.{u} ℤ G)
    (hχ : hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K) A) :
    let v := localIntegerValuation K
    let F := LocalField.ofWithZeroValuation v
    let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
    let q := F.residueCharacteristic
    let d := Module.finrank ℚ_[q] K
    Nat.card (H 1 A) = Nat.card (H 0 A) * Nat.card (H 2 A) *
      q ^ (d * padicValNat q (Nat.card A)) := by
  intro v F context q d
  let c (i : ℕ) := Nat.card (H i A)
  let b := d * padicValNat q (Nat.card A)
  let e (i : ℕ) := continuousModuleHomologyIso G A i
  have hc (i : ℕ) : Nat.card (((C).obj A).homology i) = c i :=
    Nat.card_congr (Equiv.ofBijective (e i).hom (ConcreteCategory.bijective_of_isIso (e i).hom))
  have hr := hχ.2
  rw [lowDegreeEulerCharacteristic, hc 0, hc 1, hc 2] at hr
  change (c 0 : ℚ) * (c 2 : ℚ) / (c 1 : ℚ) = (q : ℚ)⁻¹ ^ b at hr
  let : Finite (((C).obj A).homology 1) := hχ.1 1 (by decide)
  have h1 : (c 1 : ℚ) ≠ 0 := by
    rw [← hc 1]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hq : (q : ℚ) ^ b ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr F.residueCharacteristic_prime.ne_zero)
  rw [inv_pow, div_eq_iff h1] at hr
  have hQ : (c 1 : ℚ) = (c 0 : ℚ) * (c 2 : ℚ) * (q : ℚ) ^ b := by
    calc
      (c 1 : ℚ) = ((q : ℚ) ^ b * ((q : ℚ) ^ b)⁻¹) * (c 1 : ℚ) := by
        rw [mul_inv_cancel₀ hq, one_mul]
      _ = (q : ℚ) ^ b * ((c 0 : ℚ) * (c 2 : ℚ)) := by rw [mul_assoc, ← hr]
      _ = _ := mul_comm _ _
  change c 1 = c 0 * c 2 * q ^ b
  exact_mod_cast hQ

end MixedEuler

private theorem openRestriction_injective_of_primeToIndex {Γ : Type u} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (p : ℕ) [Fact p.Prime] (A : TopRep.{u} ℤ Γ) (U : OpenSubgroup Γ)
    (hp : ∀ a : A, p • a = 0) (hpU : ¬ p ∣ U.toSubgroup.index)
    (i : ℕ) (hi : i < 3) : Function.Injective (openRestriction A U i) := by
  have hindex (x : H i A) : corestrict A U i (openRestriction A U i x) =
      U.toSubgroup.index • x := by
    interval_cases i
    · exact corestrict_openRestriction_zero A U x
    · exact corestrict_openRestriction_one U A x
    · exact corestrict_openRestriction_two A U x
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  have hp' : p • (x - y) = 0 := nsmul_continuousCohomology_eq_zero_of_coefficients A p hp i _
  have ho : addOrderOf (x - y) = p := addOrderOf_eq_prime hp' hne
  have hz : U.toSubgroup.index • (x - y) = 0 := by
    rw [← hindex, map_sub, hxy, sub_self, map_zero]
  exact hpU (ho ▸ addOrderOf_dvd_of_nsmul_eq_zero hz)

private theorem finite_moduleHomology_of_pGroup_image {Γ : Type u} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    (p i : ℕ) [Fact p.Prime]
    (hT : Finite (((continuousModuleComplexFunctor Γ).obj
      (trivialIntegralZModPLifted p Γ)).homology i))
    (A : TopRep.{u} ℤ Γ) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : Γ × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0)
    (hρ : let _ : Module ℤ A := A.hV2; IsPGroup p A.ρ.toRepresentation.asGroupHom.range) :
    Finite (((continuousModuleComplexFunctor Γ).obj A).homology i) := by
  let F := continuousModuleComplexFunctor Γ
  refine finiteCoefficient_of_pGroup_image Γ p (fun X => Finite ((F.obj X).homology i))
    ?_ ?_ hT A hA hp hρ
  · intro X _
    let : Subsingleton ((F.obj X).homology i) := ModuleCat.isZero_iff_subsingleton.mp
      (continuousModuleHomology_isZero_of_subsingleton Γ X i)
    infer_instance
  · intro X Y _ _ _ _ f hf hX hY hI hQ
    let S := (coefficientRangeShortComplex ℤ Γ X Y f).map F
    let : Finite (S.X₁.homology i) := hI
    let : Finite (S.X₃.homology i) := hQ
    exact (finite_homology_of_shortExact S
      (coefficientRangeContinuousModule_shortExact Γ X Y f hf hX hY) i).1

private theorem finite_local_prime_moduleHomology_of_primitive (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hpK : (p : K) ≠ 0)
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0)
    (i : ℕ) (hi : i < 3) : Finite (((C).obj A).homology i) := by
  obtain ⟨U, hpU, hρ⟩ := exists_openSubgroup_primeToIndex_pGroup_image ℤ G A hA p
  let I := ↥(U : Subgroup G)
  let B := TopRep.res U.toSubgroup.subtype A
  let T := trivialIntegralZModPLifted p I
  obtain ⟨E, hE, hfix, _⟩ := KummerTheory.exists_finiteIntermediateField_openSubgroup_equiv_apply U
  let : FiniteDimensional K E := hE
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let e := fixedFieldAbsoluteEquiv K U E hfix
  let G' := Gal(SeparableClosure E/E)
  let T' := TopRep.res e.toMonoidHom T
  have hζE : IsPrimitiveRoot (algebraMap K E ζ) p :=
    hζ.map_of_injective (f := algebraMap K E) (algebraMap K E).injective
  have hpE : (p : E) ≠ 0 := by
    simpa only [map_natCast, map_zero] using (algebraMap K E).injective.ne hpK
  let : Finite (((continuousModuleComplexFunctor G').obj T').homology i) :=
    finite_trivialPrimeHomology_of_primitive E p hζE hpE i hi
  let : Finite (H i T') := Finite.of_injective (continuousModuleHomologyIso G' T' i).inv
    (ConcreteCategory.bijective_of_isIso (continuousModuleHomologyIso G' T' i).inv).1
  let : Finite (H i T) := Finite.of_injective (map (e : G' →ₜ* I) (𝟙 T') i)
    (restriction_equiv_injective e T i)
  let : Finite (((continuousModuleComplexFunctor I).obj T).homology i) :=
    Finite.of_injective (continuousModuleHomologyIso I T i).hom
      (ConcreteCategory.bijective_of_isIso (continuousModuleHomologyIso I T i).hom).1
  have hB : Continuous (fun gb : I × B => B.ρ gb.1 gb.2) :=
    hA.comp (continuous_subtype_val.prodMap continuous_id)
  let : Finite (((continuousModuleComplexFunctor I).obj B).homology i) :=
    let : LocallyCompactSpace I := U.isOpen'.isLocallyClosed.locallyCompactSpace
    finite_moduleHomology_of_pGroup_image p i inferInstance B hB hp hρ
  let : Finite (H i B) := Finite.of_injective (continuousModuleHomologyIso I B i).inv
    (ConcreteCategory.bijective_of_isIso (continuousModuleHomologyIso I B i).inv).1
  let : Finite (H i A) := Finite.of_injective (openRestriction A U i)
    (openRestriction_injective_of_primeToIndex p A U hp hpU i hi)
  exact Finite.of_injective (continuousModuleHomologyIso G A i).hom
    (ConcreteCategory.bijective_of_isIso (continuousModuleHomologyIso G A i).hom).1

private theorem finite_local_prime_moduleHomology (p : ℕ) [Fact p.Prime] (hpK : (p : K) ≠ 0)
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0)
    (i : ℕ) (hi : i < 3) : Finite (((C).obj A).homology i) := by
  obtain ⟨E, hE, ζ, hζ, hpU⟩ := exists_primitiveRoot_finite_stage_primeToIndex K p hpK
  let : FiniteDimensional K E := hE
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let U := stageOpenFixingSubgroup K E
  let I := ↥(U : Subgroup G)
  let B := TopRep.res U.toSubgroup.subtype A
  let e := fixedFieldAbsoluteEquiv K U E rfl
  let G' := Gal(SeparableClosure E/E)
  let B' := TopRep.res e.toMonoidHom B
  have hpE : (p : E) ≠ 0 := by
    simpa only [map_natCast, map_zero] using (algebraMap K E).injective.ne hpK
  have hB' : Continuous (fun gb : G' × B' => B'.ρ gb.1 gb.2) :=
    hA.comp ((continuous_subtype_val.comp e.continuous).prodMap continuous_id)
  let : Finite (((continuousModuleComplexFunctor G').obj B').homology i) :=
    finite_local_prime_moduleHomology_of_primitive E p hζ hpE B' hB' hp i hi
  let : Finite (H i B') := Finite.of_injective (continuousModuleHomologyIso G' B' i).inv
    (ConcreteCategory.bijective_of_isIso (continuousModuleHomologyIso G' B' i).inv).1
  let : Finite (H i B) := Finite.of_injective (map (e : G' →ₜ* I) (𝟙 B') i)
    (restriction_equiv_injective e B i)
  let : Finite (H i A) := Finite.of_injective (openRestriction A U i)
    (openRestriction_injective_of_primeToIndex p A U hp hpU i hi)
  exact Finite.of_injective (continuousModuleHomologyIso G A i).hom
    (ConcreteCategory.bijective_of_isIso (continuousModuleHomologyIso G A i).hom).1

/-- Finite discrete coefficients of invertible exponent have finite actual
continuous cohomology through degree two in any characteristic. -/
theorem finite_localIntegralCohomology_lt_three_of_exponent
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (m : ℕ) (hm : (m : K) ≠ 0) (hmA : ∀ a : A, m • a = 0)
    (i : ℕ) (hi : i < 3) : Finite (H i A) := by
  let P (X : TopRep.{u} ℤ G) : Prop := ∀ (n : ℕ), (n : K) ≠ 0 →
    (∀ x : X, n • x = 0) → Finite (((C).obj X).homology i)
  have hfin : P A := by
    refine finiteCoefficient_of_prime_coefficients G P ?_ ?_ ?_ A hA
    · intro X _ n hn hnX
      let : Subsingleton (((C).obj X).homology i) := ModuleCat.isZero_iff_subsingleton.mp
        (continuousModuleHomology_isZero_of_subsingleton G X i)
      infer_instance
    · intro X Y _ _ _ _ f hf hX hY hI hQ n hn hnY
      let : Module ℤ X := X.hV2
      let : Module ℤ Y := Y.hV2
      let W := LinearMap.range f.hom.toContinuousLinearMap.toLinearMap
      let hW := coefficientMapRange_invariant ℤ G X Y f
      let Q := invariantCoefficientQuotient ℤ G Y W hW
      let q := invariantCoefficientQuotientProjection ℤ G Y W hW
      have hnX (x : X) : n • x = 0 := by
        apply hf
        change f.hom (n • x) = f.hom 0
        rw [map_nsmul, map_zero, hnY]
      have hnQ (y : Q) : n • y = 0 := by
        obtain ⟨y, rfl⟩ := invariantCoefficientQuotientProjection_surjective ℤ G Y W hW y
        change n • q.hom y = 0
        rw [← map_nsmul, hnY, map_zero]
      let S := (coefficientRangeShortComplex ℤ G X Y f).map C
      let : Finite (S.X₁.homology i) := hI n hn hnX
      let : Finite (S.X₃.homology i) := hQ n hn hnQ
      exact (finite_homology_of_shortExact S
        (coefficientRangeContinuousModule_shortExact G X Y f hf hX hY) i).1
    · intro p hp X _ _ hX hpX n hn hnX
      by_cases hpK : (p : K) = 0
      · let : CharP K p := (CharP.charP_iff_prime_eq_zero (R := K) hp.out).mpr hpK
        have hzero (x : X) : x = 0 := by
          by_contra hx
          have horder : addOrderOf x = p := addOrderOf_eq_prime (hpX x) hx
          have hdvd : p ∣ n := horder ▸ addOrderOf_dvd_of_nsmul_eq_zero (hnX x)
          exact hn ((CharP.cast_eq_zero_iff K p n).mpr hdvd)
        let : Subsingleton X := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
        let : Subsingleton (((C).obj X).homology i) := ModuleCat.isZero_iff_subsingleton.mp
          (continuousModuleHomology_isZero_of_subsingleton G X i)
        infer_instance
      · exact finite_local_prime_moduleHomology K p hpK X hX hpX i hi
  let : Finite (((C).obj A).homology i) := hfin m hm hmA
  exact Finite.of_injective (continuousModuleHomologyIso G A i).inv
    (ConcreteCategory.bijective_of_isIso (continuousModuleHomologyIso G A i).inv).1

/-- In mixed characteristic no additional exponent condition is needed. -/
theorem finite_localIntegralCohomology_lt_three [CharZero K]
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (i : ℕ) (hi : i < 3) : Finite (H i A) :=
  finite_localIntegralCohomology_lt_three_of_exponent K A hA (Nat.card A)
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (fun _ => card_nsmul_eq_zero') i hi

end ClassFieldTheory.Brauer
