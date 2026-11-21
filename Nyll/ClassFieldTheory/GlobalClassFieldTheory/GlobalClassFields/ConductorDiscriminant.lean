/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianCharacterConductorIdeal
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorDifferentLocalization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorDiscriminantLocal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.RelativeDiscriminant
import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FirstRamificationComparison
import Nyll.ValuedFieldTheory.Ramification.LocalField.InertiaCard
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Conductor multiplicities and the global different -/

@[expose] public section

open scoped NumberField ValuativeRel nonZeroDivisors IsMulCommutative
open ClassFieldTheory
open NumberField IsDedekindDomain AlgebraicNumberTheory AlgebraicNumberTheory.Valuations
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open RamificationTheory.HilbertRamification RamificationTheory.LocalField

noncomputable section
namespace GlobalClassFieldTheory.GlobalClassFields

open Reciprocity

universe u v

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

private theorem card_localLowerRamificationGroup_zero
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    let base := localCompleteDVF F
    let target := chosenLocalExtensionCompleteDVF F E
    Nat.card (localLowerRamificationGroup F E 0) = ramificationIndex base.toDVF target.toDVF := by
  intro base target
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, u, v, 0, 0}
        base.toDVF target.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension F E
  let I := CompleteDVF.inertiaGroup (base := base) (target := target)
  have hI : localLowerRamificationGroup F E 0 = I :=
    Subgroup.ext fun σ =>
      mem_lowerRamificationGroup_zero_iff_completeDVF_inertiaGroup base target huniq σ
  let q := CompleteDVF.galEquivDecompositionGroup (base := base) (target := target)
  calc
    Nat.card (localLowerRamificationGroup F E 0) = Nat.card (I.map q.toMonoidHom) := by
      rw [hI, Subgroup.card_map_of_injective q.injective]
    _ = Nat.card (target.valuation.valuationSubring.inertiaSubgroup F) := by
      change Nat.card ((CompleteDVF.inertiaGroup base target).map
        (CompleteDVF.galEquivDecompositionGroup base target).toMonoidHom) = _
      rw [CompleteDVF.inertiaGroup_map_galEquivDecompositionGroup]
    _ = _ := chosenLocalExtension_inertia_card_eq_ramificationIndex F E

private theorem completeDVF_maximalIdeal_exponent_eq_of_pow_eq
    {J : Type*} [Field J] (D : ValuationTheory.DiscreteValuationField.CompleteDVF J) {d e : ℕ}
    (h : D.maximalIdeal ^ d = D.maximalIdeal ^ e) : d = e := by
  let : IsFractionRing D.valuationSubring J := D.toDVF.valuationSubring_isFractionRing
  let : IsDiscreteValuationRing D.valuationSubring :=
    D.toDVF.valuationSubring_isDiscreteValuationRing
  have order := RamificationTheory.DiscreteValuationRing.maximalIdeal_pow_le_iff
    D.valuationSubring J
  exact le_antisymm ((order e d).mp h.ge) ((order d e).mp h.le)

private theorem completedDifferent_exponent_eq_multiplicity_and_ramificationIndex
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) (d : ℕ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let base := localCompleteDVF vK.Completion
    let target := chosenLocalExtensionCompleteDVF vK.Completion E
    let : IsScalarTower base.valuationSubring target.valuationSubring E :=
      IsScalarTower.of_algebraMap_eq' rfl
    RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
        base target = target.maximalIdeal ^ d →
      ramificationIndex base.toDVF target.toDVF =
        v.asIdeal.ramificationIdx' (finitePlaceExtensionCentre v w).asIdeal ∧
      d = multiplicity (finitePlaceExtensionCentre v w).asIdeal (differentIdeal (𝓞 K) (𝓞 L)) := by
  intro vK E algebraOwner finiteOwner abelianOwner valuationOwner localFieldOwner
    base target towerOwner hd
  obtain ⟨j, _, hj, hjpre, hram, hmap⟩ := exists_map_differentIdeal_eq_completedDifferent v w
  let I := differentIdeal (𝓞 K) (𝓞 L)
  let P := finitePlaceExtensionCentre v w
  have hdmap := map_ideal_eq_maximalIdeal_pow_multiplicity j P I
    (Discriminant.relativeDifferentIdeal_ne_bot K L) hj hjpre
  have hpowers := hd.symm.trans (hmap.symm.trans hdmap)
  refine ⟨hram, ?_⟩
  have hexponent := completeDVF_maximalIdeal_exponent_eq_of_pow_eq target
    (d := d) (e := multiplicity P.asIdeal I)
  dsimp (config := { instances := true, zetaDelta := true }) only
    [target, base, E, vK, algebraOwner, finiteOwner, abelianOwner, valuationOwner,
      localFieldOwner, towerOwner, I, P] at hexponent hpowers
  with_reducible exact hexponent hpowers

/-- At every prime over `v`, the conductor sum times the ramification index
equals the actual different multiplicity times the Galois order. -/
theorem ramificationIdx_mul_finsum_characterConductor_eq_card_mul_differentMultiplicity
    (v : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    (hP : finitePlaceBelow (K := K) P = v) :
    v.asIdeal.ramificationIdx' P.asIdeal *
      (∑ᶠ χ : Gal(L / K) →* ℂˣ, (abelianCharacterConductor K L χ).finitePart v) =
      Nat.card Gal(L / K) * multiplicity P.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let placeEquiv := finitePlaceExtensionEquivAbove (L := L) v
  let w := placeEquiv.symm ⟨P, hP⟩
  have hcentre : finitePlaceExtensionCentre v w = P :=
    congrArg Subtype.val (placeEquiv.apply_symm_apply ⟨P, hP⟩)
  let E := LocalizedCompletion vK w
  let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
  let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w inferInstance
  let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let F := vK.Completion
  obtain ⟨d, hd, hsum⟩ :=
    exists_completedDifferent_eq_pow_and_card_mul_finsum_characterConductor_of_extension v w
  obtain ⟨hram, hdeq⟩ := completedDifferent_exponent_eq_multiplicity_and_ramificationIndex v w d hd
  have hcard := card_localLowerRamificationGroup_zero F E
  dsimp (config := { instances := true, zetaDelta := true }) only [F, E, vK] at hcard
  rw [hcard, hram, hdeq, hcentre] at hsum
  exact hsum

/-- The coefficient of a finite prime in the relative ideal discriminant is
the sum of the conductor exponents of all the complex Galois characters. -/
theorem count_relativeDiscriminantIdeal_eq_finsum_characterConductor
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (Discriminant.relativeDiscriminantIdeal K L : FractionalIdeal (𝓞 K)⁰ K) =
      ((∑ᶠ χ : Gal(L / K) →* ℂˣ, (abelianCharacterConductor K L χ).finitePart v) : ℕ) := by
  classical
  let : Module.Finite ℤ (𝓞 L) := inferInstance
  let : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let : Module.IsTorsionFree (𝓞 K) (𝓞 L) := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (fun _ _ h => Subtype.ext ((algebraMap K L).injective (congrArg Subtype.val h)))
  let : IsGaloisGroup Gal(L / K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L / K) (𝓞 K) (𝓞 L) K L
  let p := v.asIdeal
  let : p.IsPrime := v.isPrime
  let T := {P : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) P = v}
  let Tfin := finite_finitePlaceBelow_fibre (K := K) (L := L) v
  let : Fintype T := Tfin.fintype
  let Q := p.primesOver (𝓞 L)
  let : Fintype Q := (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 L) p).fintype
  let toAbove (x : T) : Q :=
    ⟨x.1.asIdeal, x.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal x.2).symm⟩⟩
  have hto : Function.Bijective toAbove := by
    constructor
    · intro x y h
      exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · intro q
      let : q.1.LiesOver p := q.2.2
      have hq : q.1 ≠ ⊥ := by
        intro hz
        have hle : p.map (algebraMap (𝓞 K) (𝓞 L)) ≤ q.1 :=
          Ideal.map_le_iff_le_comap.mpr (show p ≤ q.1.under (𝓞 K) from (Ideal.over_def q.1 p).le)
        exact (Ideal.map_ne_bot_of_ne_bot v.ne_bot) (le_bot_iff.mp (hz ▸ hle))
      let P : HeightOneSpectrum (𝓞 L) := ⟨q.1, q.2.1, hq⟩
      exact ⟨⟨P, HeightOneSpectrum.ext (Ideal.over_def q.1 p).symm⟩, Subtype.ext rfl⟩
  let e := Equiv.ofBijective toAbove hto
  let degree (x : T) := x.1.asIdeal.inertiaDeg (𝓞 K)
  let ram (x : T) := p.ramificationIdx' x.1.asIdeal
  let D := differentIdeal (𝓞 K) (𝓞 L)
  let d (x : T) := multiplicity x.1.asIdeal D
  let c := ∑ᶠ χ : Gal(L / K) →* ℂˣ, (abelianCharacterConductor K L χ).finitePart v
  let g := Nat.card Gal(L / K)
  have hf : (∑ x : T, ram x * degree x) = g := by
    calc
      (∑ x : T, ram x * degree x) = ∑ q : Q, q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) := by
        refine Fintype.sum_equiv e _ _ fun x => ?_
        let : x.1.asIdeal.LiesOver p := (toAbove x).2.2
        change p.ramificationIdx' x.1.asIdeal * degree x =
          x.1.asIdeal.ramificationIdx (𝓞 K) * degree x
        rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
      _ = g := Ideal.sum_ramification_inertia_eq_card p (𝓞 L) (G := Gal(L / K))
  have hsum : (∑ x : T, degree x * d x) = c := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < g from Finite.card_pos)
    calc
      g * (∑ x : T, degree x * d x) = ∑ x : T, degree x * (g * d x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ac_rfl
      _ = ∑ x : T, (ram x * degree x) * c := by
        apply Finset.sum_congr rfl
        intro x _
        have hx : ram x * c = g * d x :=
          ramificationIdx_mul_finsum_characterConductor_eq_card_mul_differentMultiplicity v x.1 x.2
        calc
          _ = degree x * (ram x * c) := congrArg (degree x * ·) hx.symm
          _ = _ := by ac_rfl
      _ = g * c := by rw [← Finset.sum_mul, hf]
  let Dexp :=
    NumberFieldFractionalIdealGroup.countVector (Discriminant.relativeDifferentFractionalIdeal K L)
  have hDexp (P : HeightOneSpectrum (𝓞 L)) : Dexp P = (multiplicity P.asIdeal D : ℤ) := by
    have hD : D ≠ ⊥ := Discriminant.relativeDifferentIdeal_ne_bot K L
    change FractionalIdeal.count L P (D : FractionalIdeal (𝓞 L)⁰ L) = _
    exact ClassFieldTheory.FractionalIdealFactorization.count_coeIdeal_eq_multiplicity (F := L) P hD
  let s := Tfin.toFinset
  let f (P : HeightOneSpectrum (𝓞 L)) :=
    if finitePlaceBelow (K := K) P = v then (P.asIdeal.inertiaDeg (𝓞 K) : ℤ) * Dexp P else 0
  have hcount : (∑ P ∈ Dexp.support, f P) = ∑ x : T, ((degree x * d x : ℕ) : ℤ) := by
    calc
      (∑ P ∈ Dexp.support, f P) = ∑ P ∈ Dexp.support ∪ s, f P := by
        refine Finset.sum_subset Finset.subset_union_left fun P _ hP => ?_
        have hz := Finsupp.notMem_support_iff.mp hP
        simp only [f, hz, mul_zero, ite_self]
      _ = ∑ P ∈ s, f P := by
        refine (Finset.sum_subset Finset.subset_union_right fun P _ hP => ?_).symm
        exact ite_eq_right (fun hp => hP (Tfin.mem_toFinset.mpr hp))
      _ = ∑ x : T, f x.1 := Finset.sum_subtype _ (fun _ => Tfin.mem_toFinset) _
      _ = ∑ x : T, ((degree x * d x : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _
        change (if finitePlaceBelow (K := K) x.1 = v then
          (x.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * Dexp x.1 else 0) = _
        rw [ite_eq_left x.2, hDexp, Nat.cast_mul]
  rw [Discriminant.count_relativeDiscriminantIdeal K L v, Finsupp.sum]
  change (∑ P ∈ Dexp.support, f P) = (c : ℤ)
  rw [hcount, ← Nat.cast_sum, hsum]

/-- The conductor–discriminant formula for a finite abelian number field
extension, as an equality of the genuine relative ideal discriminant and
the product of the finite parts of all complex character conductors. -/
theorem relativeDiscriminantIdeal_eq_finprod_characterConductor :
    Discriminant.relativeDiscriminantIdeal K L =
      ∏ᶠ χ : Gal(L / K) →* ℂˣ, abelianCharacterFiniteConductorIdeal χ := by
  classical
  let g := Nat.card Gal(L / K)
  let : NeZero g := ⟨Finite.card_pos.ne'⟩
  let : NeZero (g : ℂ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne g)⟩
  let : HasEnoughRootsOfUnity ℂ g := IsSepClosed.hasEnoughRootsOfUnity ℂ g
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent Gal(L / K)) :=
    HasEnoughRootsOfUnity.of_dvd ℂ (n := g) (Group.exponent_dvd_nat_card (G := Gal(L / K)))
  let : Fintype (Gal(L / K) →* ℂˣ) := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  let P : Ideal (𝓞 K) := ∏ χ : Gal(L / K) →* ℂˣ, abelianCharacterFiniteConductorIdeal χ
  have hP : P ≠ ⊥ := Finset.prod_ne_zero_iff.mpr fun χ _ =>
    abelianCharacterFiniteConductorIdeal_ne_bot χ
  let d := FractionalIdeal.mk0 K ⟨Discriminant.relativeDiscriminantIdeal K L,
    mem_nonZeroDivisors_iff_ne_zero.mpr (Discriminant.relativeDiscriminantIdeal_ne_bot K L)⟩
  let C := FractionalIdeal.mk0 K ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hP⟩
  have h : d = C := by
    apply NumberFieldFractionalIdealGroup.ext_count
    intro v
    change FractionalIdeal.count K v
        (Discriminant.relativeDiscriminantIdeal K L : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K v (P : FractionalIdeal (𝓞 K)⁰ K)
    rw [count_relativeDiscriminantIdeal_eq_finsum_characterConductor,
      count_prod_abelianCharacterFiniteConductorIdeal, finsum_eq_sum_of_fintype, Nat.cast_sum]
  exact (FractionalIdeal.coeIdeal_inj (K := K)).mp (congrArg Units.val h)

end GlobalClassFieldTheory.GlobalClassFields
