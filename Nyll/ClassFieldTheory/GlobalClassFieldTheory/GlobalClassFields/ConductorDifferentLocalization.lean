/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.DifferentTraceLocalization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalizedValuation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ValuedFieldTheory.Ramification.Different
public import Nyll.ValuedFieldTheory.Ramification.LocalField.Core
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Extended

/-! # Localization of the global different in the actual finite Artin completion -/

@[expose] public section

open scoped NumberField ValuativeRel nonZeroDivisors
open NumberField IsDedekindDomain AlgebraicNumberTheory AlgebraicNumberTheory.Valuations
open LocalFieldTheory ValuationTheory.DiscreteValuationField.ValuedExtension
open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open _root_.RamificationTheory.DiscreteValuationField.ValuedExtension

noncomputable section
namespace GlobalClassFieldTheory.GlobalClassFields

open Reciprocity

/-- A map to a local ring retains exactly the power of the prime below its
maximal ideal if that prime extends with exponent one. -/
theorem map_ideal_eq_maximalIdeal_pow_multiplicity
    {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsLocalRing S]
    (j : R →+* S) (P : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ ⊥)
    (hP : P.asIdeal.map j = IsLocalRing.maximalIdeal S)
    (hpre : (IsLocalRing.maximalIdeal S).comap j = P.asIdeal) :
    I.map j = IsLocalRing.maximalIdeal S ^ multiplicity P.asIdeal I := by
  classical
  let f (Q : HeightOneSpectrum R) := Q.asIdeal ^ multiplicity Q.asIdeal I
  let s := insert P (Ideal.finite_factors hI).toFinset
  have hs : Function.mulSupport f ⊆ s := by
    intro Q hQ
    apply Finset.mem_insert_of_mem
    apply (Ideal.finite_factors hI).mem_toFinset.mpr
    have hpos : 0 < multiplicity Q.asIdeal I := by
      apply Nat.pos_iff_ne_zero.mpr
      intro hzero
      exact hQ (by simp only [f, hzero, pow_zero])
    have h := (FiniteMultiplicity.of_prime_left Q.prime hI).pow_dvd_iff_le_multiplicity
      (k := 1)
    rw [pow_one] at h
    exact h.mpr hpos
  have hfactor : (∏ Q ∈ s, f Q) = I :=
    (finprod_eq_prod_of_mulSupport_subset f hs).symm.trans
      (Ideal.finprod_heightOneSpectrum_pow_multiplicity hI)
  conv_lhs => rw [← hfactor]
  rw [← Ideal.mapHom_apply, map_prod]
  simp only [f, Ideal.mapHom_apply, Ideal.map_pow]
  rw [Finset.prod_eq_single P, hP]
  · intro Q _ hQP
    have hQtop : Q.asIdeal.map j = ⊤ := by
      by_contra hQ
      have hle := Ideal.map_le_iff_le_comap.mp (IsLocalRing.le_maximalIdeal hQ)
      rw [hpre] at hle
      exact hQP (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))
    rw [hQtop, ← Ideal.one_eq_top, one_pow]
  · exact fun h => (h (Finset.mem_insert_self _ _)).elim

private def ringEquiv_on_subrings {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (A : Subring R) (B : Subring S)
    (he : ∀ x : R, e x ∈ B ↔ x ∈ A) : A ≃+* B where
  toFun x := ⟨e x.val, (he x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (he (e.symm y.val)).mp
    ((e.apply_symm_apply y.val).symm ▸ y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)

private theorem map_comap_prime_of_equivalent_targets
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (j : R →+* A) (k : R →+* B) (e : A ≃+* B)
    (P : Ideal R) (I : Ideal A) (J : Ideal B)
    (hcomp : e.toRingHom.comp j = k) (hIJ : I.map e.toRingHom = J)
    (hmap : P.map k = J) (hback : J.comap k = P) :
    P.map j = I ∧ I.comap j = P := by
  let f := e.toRingHom
  have hm : (P.map j).map f = I.map f :=
    (Ideal.map_map j f).trans ((congrArg (Ideal.map · P) hcomp).trans (hmap.trans hIJ.symm))
  have hc : J.comap f = I :=
    (congrArg (Ideal.comap f) hIJ).symm.trans (Ideal.comap_map_of_bijective f e.bijective)
  have hck : (J.comap f).comap j = P :=
    (Ideal.comap_comap j f).trans ((congrArg (fun r => J.comap r) hcomp).trans hback)
  exact ⟨e.idealComapOrderIso.symm.injective hm, (congrArg (Ideal.comap j) hc).symm.trans hck⟩

private theorem ramificationIndex_eq_of_integer_maps
    {R S A B E : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field E] [Algebra B E] [IsFractionRing B E] [Algebra R S] [FaithfulSMul R S]
    (v : HeightOneSpectrum R) (P : HeightOneSpectrum S)
    (jA : R →+* A) (j : S →+* B) (b : A →+* B) (r : ℕ)
    (hsquare : b.comp jA = j.comp (algebraMap R S))
    (hA : v.asIdeal.map jA = IsLocalRing.maximalIdeal A)
    (hP : P.asIdeal.map j = IsLocalRing.maximalIdeal B)
    (hPback : (IsLocalRing.maximalIdeal B).comap j = P.asIdeal)
    (hpow : (IsLocalRing.maximalIdeal A).map b = IsLocalRing.maximalIdeal B ^ r) :
    r = v.asIdeal.ramificationIdx' P.asIdeal := by
  let I := v.asIdeal.map (algebraMap R S)
  have hI : I ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hmult : v.asIdeal.ramificationIdx' P.asIdeal = multiplicity P.asIdeal I :=
    Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hI P.isPrime
  have hpowers : IsLocalRing.maximalIdeal B ^ r =
      IsLocalRing.maximalIdeal B ^ v.asIdeal.ramificationIdx' P.asIdeal := calc
    _ = (IsLocalRing.maximalIdeal A).map b := hpow.symm
    _ = (v.asIdeal.map jA).map b := congrArg (Ideal.map b) hA.symm
    _ = v.asIdeal.map (b.comp jA) := Ideal.map_map jA b
    _ = v.asIdeal.map (j.comp (algebraMap R S)) := congrArg (v.asIdeal.map ·) hsquare
    _ = I.map j := (Ideal.map_map (algebraMap R S) j).symm
    _ = IsLocalRing.maximalIdeal B ^ multiplicity P.asIdeal I :=
      map_ideal_eq_maximalIdeal_pow_multiplicity j P I hI hP hPback
    _ = _ := congrArg (IsLocalRing.maximalIdeal B ^ ·) hmult.symm
  exact le_antisymm
    ((RamificationTheory.DiscreteValuationRing.maximalIdeal_pow_le_iff B E _ _).mp hpowers.ge)
    ((RamificationTheory.DiscreteValuationRing.maximalIdeal_pow_le_iff B E _ _).mp hpowers.le)

private theorem exists_lowerCompletionIntegerMap
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (base : ValuationTheory.DiscreteValuationField.CompleteDVF
      (HeightOneSpectrum.adicAbv K v).Completion)
    (hbase : ∀ x : (HeightOneSpectrum.adicAbv K v).Completion,
      x ∈ base.valuation.valuationSubring ↔
        x ∈ absoluteValueCompletionIntegers (HeightOneSpectrum.adicAbv K v)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v)) :
    ∃ j : 𝓞 K →+* base.valuationSubring,
      (∀ x : 𝓞 K, (j x : (HeightOneSpectrum.adicAbv K v).Completion) =
        algebraMap K (HeightOneSpectrum.adicAbv K v).Completion (x : K)) ∧
      v.asIdeal.map j = base.maximalIdeal := by
  let F := (HeightOneSpectrum.adicAbv K v).Completion
  let A := base.valuation.valuationSubring
  let eK := finitePlaceCompletionRingEquiv v
  have heK (x : F) : eK x ∈ v.adicCompletionIntegers K ↔ x ∈ A := by
    rw [hbase, mem_absoluteValueCompletionIntegers_iff]
    constructor
    · intro hx
      have h := norm_le_one_of_mem_adicCompletionIntegers v hx
      rwa [finitePlaceCompletionRingEquiv_norm] at h
    · intro hx
      apply mem_adicCompletionIntegers_of_norm_le_one v
      rwa [finitePlaceCompletionRingEquiv_norm]
  let eA : A ≃+* v.adicCompletionIntegers K :=
    ringEquiv_on_subrings eK A.toSubring (v.adicCompletionIntegers K).toSubring heK
  let kA : 𝓞 K →+* v.adicCompletionIntegers K :=
    algebraMap (𝓞 K) (v.adicCompletionIntegers K)
  let jA : 𝓞 K →+* A := eA.symm.toRingHom.comp kA
  have hjA (x : 𝓞 K) : (jA x : F) = algebraMap K F (x : K) := by
    apply eK.injective
    change eK (eK.symm _) = eK (algebraMap K F (x : K))
    rw [RingEquiv.apply_symm_apply]
    exact ((finitePlaceCompletionAlgEquiv v).commutes (x : K)).symm
  have heA := IsLocalRing.map_maximalIdeal_of_surjective eA.toRingHom eA.surjective
  have hAK : base.maximalIdeal.map eA.toRingHom = v.completionIdeal K := heA
  have hKA : v.asIdeal.map kA = v.completionIdeal K :=
    v.map_asIdeal_adicCompletionIntegers (K := K)
  have hkb : eA.toRingHom.comp jA = kA := by
    apply RingHom.ext
    intro x
    exact eA.apply_symm_apply (kA x)
  have hA : v.asIdeal.map jA = base.maximalIdeal := by
    apply eA.idealComapOrderIso.symm.injective
    exact (Ideal.map_map jA eA.toRingHom).trans
      ((congrArg (fun f => v.asIdeal.map f) hkb).trans (hKA.trans hAK.symm))
  exact ⟨jA, hjA, hA⟩

private theorem span_eq_traceDual_one_of_algEquiv
    {A B O F E C : Type*} [CommRing A] [CommRing B] [CommRing O]
    [Field F] [Field E] [Field C] [Algebra F E] [Algebra F C]
    [Algebra A F] [Algebra A B] [Algebra A E] [Algebra B E] [Algebra O C]
    [IsScalarTower A F E] [IsScalarTower A B E]
    (e : E ≃ₐ[F] C) (g : B ≃+* O)
    (h : ∀ b : B, e (algebraMap B E b) = algebraMap O C (g b))
    (s : Set E) (integers : Set F)
    (hA : ∀ z : F, z ∈ (algebraMap A F).range ↔ z ∈ integers)
    (hSpan : ∀ z : C, z ∈ Submodule.span O (e '' s) ↔
      ∀ b : O, Algebra.trace F C (z * algebraMap O C b) ∈ integers) :
    Submodule.span B s = Submodule.traceDual A F (1 : Submodule B E) := by
  let : RingHomSurjective g.toRingHom := ⟨g.surjective⟩
  let f : E →ₛₗ[g.toRingHom] C :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun b x => by
        change e (b • x) = g b • e x
        simp only [Algebra.smul_def, map_mul, h] }
  have hMap : (Submodule.span B s).map f = Submodule.span O (e '' s) :=
    Submodule.map_span f s
  apply Submodule.ext
  intro x
  have hMem : x ∈ Submodule.span B s ↔ e x ∈ Submodule.span O (e '' s) := by
    rw [← hMap, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := e.injective hxy
      exact hyx ▸ hy
  refine hMem.trans ((hSpan (e x)).trans ?_)
  rw [Submodule.mem_traceDual]
  have hTrace (b : B) :
      Algebra.trace F C (e x * algebraMap O C (g b)) =
        Algebra.trace F E (x * algebraMap B E b) := by
    rw [← h b, ← map_mul, Algebra.trace_eq_of_algEquiv e]
  constructor
  · intro hx y hy
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hy
    rw [Algebra.traceForm_apply, ← hTrace b]
    exact (hA _).mpr (hx (g b))
  · intro hx b
    obtain ⟨b, rfl⟩ := g.surjective b
    rw [hTrace b, ← hA, ← Algebra.traceForm_apply]
    exact hx _ (Submodule.mem_one.mpr ⟨b, rfl⟩)

private theorem map_differentIdeal_of_span_traceDual
    {R S A B K L F E : Type*}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [IsDedekindDomain S]
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L] [Field F] [Field E]
    [Algebra R K] [Algebra S L] [Algebra A F] [Algebra B E]
    [IsFractionRing R K] [IsFractionRing S L] [IsFractionRing A F] [IsFractionRing B E]
    [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [Algebra A B] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [IsScalarTower A B E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure S R L] [Module.IsTorsionFree R S]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [IsIntegralClosure B A E] [Module.IsTorsionFree A B]
    (j : S →+* B) (hj : Function.Injective j) (i : L →+* E)
    (hi : ∀ x : S, i (algebraMap S L x) = algebraMap B E (j x))
    (hSpan : Submodule.span B (i '' (Submodule.traceDual R K (1 : Submodule S L) : Set L)) =
      Submodule.traceDual A F (1 : Submodule B E)) :
    (differentIdeal R S).map j = differentIdeal A B := by
  let : Algebra S B := j.toAlgebra
  let : Module.IsTorsionFree S B := Module.isTorsionFree_iff_algebraMap_injective.mpr hj
  let d₁ := FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)
  let d₂ := FractionalIdeal.dual A F (1 : FractionalIdeal B⁰ E)
  let m : FractionalIdeal S⁰ L →+* FractionalIdeal B⁰ E := FractionalIdeal.extendedHom E B
  have hle : S⁰ ≤ B⁰.comap (algebraMap S B) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective S B)
  have hi' : IsLocalization.map (S := L) E (algebraMap S B) hle = i :=
    IsLocalization.map_unique hle i hi
  have hSource : (d₁ : Set L) = (Submodule.traceDual R K (1 : Submodule S L) : Set L) :=
    congrArg (fun U : Submodule S L => (U : Set L))
      (FractionalIdeal.coeToSubmodule_dual_one R K (L := L) (B := S))
  have hDual : m d₁ = d₂ := by
    apply FractionalIdeal.coeToSubmodule_injective
    change (FractionalIdeal.extendedHom E B d₁ : Submodule B E) = (d₂ : Submodule B E)
    rw [FractionalIdeal.extendedHom'_apply,
      FractionalIdeal.coeToSubmodule_extended_eq_span, hi', hSource]
    exact hSpan.trans (FractionalIdeal.coeToSubmodule_dual_one A F (L := E) (B := B)).symm
  apply FractionalIdeal.coeIdeal_injective (K := E)
  calc
    _ = m (differentIdeal R S : FractionalIdeal S⁰ L) :=
      (FractionalIdeal.extendedHom_coeIdeal_eq_map E B (differentIdeal R S)).symm
    _ = m (d₁⁻¹) := congrArg m (coeIdeal_differentIdeal R K L S)
    _ = (m d₁)⁻¹ := map_inv₀ m d₁
    _ = d₂⁻¹ := congrArg Inv.inv hDual
    _ = _ := (coeIdeal_differentIdeal A F E B).symm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

section LocalizedTrace

variable (v : HeightOneSpectrum (𝓞 K))
  (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L)

local notation "vK" => HeightOneSpectrum.adicAbv K v
local notation "hvK" => HeightOneSpectrum.isNonarchimedean_adicAbv K v
local notation "Fv" => AbsoluteValue.Completion (HeightOneSpectrum.adicAbv K v)
local notation "Cw" => AbsoluteValue.Completion (Subtype.val w)
local notation "Ow" => absoluteValueCompletionIntegers (Subtype.val w)
  (absoluteValueExtension_isNonarchimedean vK hvK w)

noncomputable local instance : Algebra Fv Cw := AbsoluteValue.completionAlgebra vK w.1 w.2

omit [IsAbelianGalois K L] in
private theorem span_globalTraceDual_eq_localizedTraceDual
    {E : Type*} [Field E] [Algebra Fv E]
    (A : ValuationSubring Fv) (B : ValuationSubring E)
    [Algebra A B] [Algebra A E] [IsScalarTower A Fv E] [IsScalarTower A B E]
    (i : L →+* E) (e : E ≃ₐ[Fv] Cw)
    (hi : ∀ x : L, e (i x) = AbsoluteValue.toCompletion w.1 x)
    (hbase : ∀ x : Fv, x ∈ A ↔ x ∈ absoluteValueCompletionIntegers vK hvK)
    (htop : ∀ x : E, x ∈ B ↔ e x ∈ Ow) :
    Submodule.span B
        (i '' (Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L) : Set L)) =
      Submodule.traceDual A Fv (1 : Submodule B E) := by
  let D := Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)
  let O := Ow
  let _ : Algebra O Cw := Algebra.ofSubsemiring O
  let eInt : B ≃+* O :=
    ringEquiv_on_subrings e.toRingEquiv B.toSubring O.toSubring (fun x => (htop x).symm)
  have hInt (b : B) : e (algebraMap B E b) = algebraMap O Cw (eInt b) := rfl
  have hA (x : Fv) :
      x ∈ (algebraMap A Fv).range ↔ x ∈ absoluteValueCompletionIntegers vK hvK := by
    refine Iff.trans ?_ (hbase x)
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hImage : e '' (i '' (D : Set L)) = AbsoluteValue.toCompletion w.1 '' (D : Set L) := by
    rw [Set.image_image]
    exact congrArg (fun f : L → Cw => f '' (D : Set L)) (funext hi)
  have hLocal := finitePlace_span_globalTraceDual_eq_localTraceDual v w
  have hSpan (z : Cw) :
      z ∈ Submodule.span O (e '' (i '' (D : Set L))) ↔
        ∀ b : O, Algebra.trace Fv Cw (z * algebraMap O Cw b) ∈
          absoluteValueCompletionIntegers vK hvK := by
    rw [hImage]
    exact Iff.of_eq (congrArg (fun T : Set Cw => z ∈ T) hLocal)
  exact span_eq_traceDual_one_of_algEquiv e eInt hInt (i '' (D : Set L)) _ hA hSpan

omit [FiniteDimensional K L] [IsAbelianGalois K L] in
private theorem ramificationIndex_eq_of_localizedIntegerMap
    {E : Type*} [Field E] [Algebra Fv E]
    (base : ValuationTheory.DiscreteValuationField.CompleteDVF Fv)
    (B : ValuationSubring E) [IsDiscreteValuationRing B] [IsFractionRing B E]
    (P : HeightOneSpectrum (𝓞 L))
    (i : L →+* E) (e : E ≃ₐ[Fv] Cw)
    (j : 𝓞 L →+* B) (b : base.valuationSubring →+* B)
    (hj : ∀ x : 𝓞 L, (j x : E) = i (x : L))
    (hb : ∀ x : base.valuationSubring, (b x : E) = algebraMap Fv E (x : Fv))
    (hi : ∀ x : L, e (i x) = AbsoluteValue.toCompletion w.1 x)
    (hbase : ∀ x : Fv, x ∈ base.valuation.valuationSubring ↔
      x ∈ absoluteValueCompletionIntegers vK hvK)
    (hP : P.asIdeal.map j = IsLocalRing.maximalIdeal B)
    (hPback : (IsLocalRing.maximalIdeal B).comap j = P.asIdeal)
    (r : ℕ) (hpow : base.maximalIdeal.map b = IsLocalRing.maximalIdeal B ^ r) :
    r = v.asIdeal.ramificationIdx' P.asIdeal := by
  obtain ⟨jA, hjA, hA⟩ := exists_lowerCompletionIntegerMap v base hbase
  have hsquare : b.comp jA = j.comp (algebraMap (𝓞 K) (𝓞 L)) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    apply e.injective
    change e (b (jA x) : E) = e (j (algebraMap (𝓞 K) (𝓞 L) x) : E)
    rw [hb, hj]
    have hleft := e.commutes (jA x : Fv)
    have hLower := congrArg (algebraMap Fv Cw) (hjA x)
    have hcoe := AbsoluteValue.completionMap_coe vK w.1 w.2 (x : K)
    have hright := hi (algebraMap K L (x : K))
    exact hleft.trans (hLower.trans (hcoe.trans hright.symm))
  exact ramificationIndex_eq_of_integer_maps
    (R := 𝓞 K) (S := 𝓞 L) (A := base.valuationSubring) (B := B) (E := E)
    v P jA j b r hsquare hA hP hPback hpow

omit [FiniteDimensional K L] [IsAbelianGalois K L] in
private theorem exists_map_comap_localizedPrime
    {E : Type*} [Field E] [Algebra Fv E]
    (B : ValuationSubring E) [IsDiscreteValuationRing B]
    (i : L →+* E) (e : E ≃ₐ[Fv] Cw)
    (hi : ∀ x : L, e (i x) = AbsoluteValue.toCompletion w.1 x)
    (htop : ∀ x : E, x ∈ B ↔ e x ∈ Ow) :
    ∃ j : 𝓞 L →+* B, (∀ a : 𝓞 L, (j a : E) = i (a : L)) ∧
      (finitePlaceExtensionCentre v w).asIdeal.map j = IsLocalRing.maximalIdeal B ∧
      (IsLocalRing.maximalIdeal B).comap j = (finitePlaceExtensionCentre v w).asIdeal := by
  let j : 𝓞 L →+* B :=
    RingHom.codRestrict (i.comp (algebraMap (𝓞 L) L)) B.toSubring (fun a =>
      (htop _).mpr (by
        change e (i (a : L)) ∈ _
        rw [hi]
        exact (finitePlaceIntegralDiagonal v a w).2))
  let P := finitePlaceExtensionCentre v w
  let eF : E ≃+* P.adicCompletion L :=
    e.toRingEquiv.trans (finitePlaceExtensionAdicCompletionRingEquiv v w)
  have heF (x : E) : eF x ∈ P.adicCompletionIntegers L ↔ x ∈ B :=
    (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff v w (e x)).trans (htop x).symm
  let eB : B ≃+* P.adicCompletionIntegers L :=
    ringEquiv_on_subrings eF B.toSubring (P.adicCompletionIntegers L).toSubring heF
  have hcomp : eB.toRingHom.comp j = algebraMap (𝓞 L) (P.adicCompletionIntegers L) := by
    apply RingHom.ext
    intro a
    apply Subtype.ext
    change finitePlaceExtensionAdicCompletionRingEquiv v w (e (i (a : L))) = _
    rw [hi]
    exact finitePlaceExtensionAdicCompletionRingEquiv_toCompletion v w (a : L)
  have hmax : (IsLocalRing.maximalIdeal B).map eB.toRingHom = P.completionIdeal L :=
    IsLocalRing.map_maximalIdeal_of_surjective eB.toRingHom eB.surjective
  have hPmap := P.map_asIdeal_adicCompletionIntegers (K := L)
  have hPcomap := (Ideal.over_def (P.completionIdeal L) P.asIdeal).symm
  have hprime := map_comap_prime_of_equivalent_targets j
    (algebraMap (𝓞 L) (P.adicCompletionIntegers L)) eB
    P.asIdeal (IsLocalRing.maximalIdeal B) (P.completionIdeal L) hcomp hmax hPmap hPcomap
  exact ⟨j, fun _ => rfl, hprime⟩

omit [IsAbelianGalois K L] in
private theorem map_globalDifferent_eq_localDifferent
    {E : Type*} [Field E] [Algebra Fv E] [FiniteDimensional Fv E] [Algebra.IsSeparable Fv E]
    (A : ValuationSubring Fv) (B : ValuationSubring E)
    [IsFractionRing A Fv] [IsFractionRing B E]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A E] [IsScalarTower A Fv E] [IsScalarTower A B E]
    [IsIntegralClosure B A E] [Module.IsTorsionFree A B]
    (i : L →+* E) (e : E ≃ₐ[Fv] Cw) (j : 𝓞 L →+* B)
    (hi : ∀ x : L, e (i x) = AbsoluteValue.toCompletion w.1 x)
    (hj : ∀ a : 𝓞 L, (j a : E) = i (a : L))
    (hbase : ∀ x : Fv, x ∈ A ↔ x ∈ absoluteValueCompletionIntegers vK hvK)
    (htop : ∀ x : E, x ∈ B ↔ e x ∈ Ow) :
    (differentIdeal (𝓞 K) (𝓞 L)).map j = differentIdeal A B := by
  let : Module.IsTorsionFree (𝓞 K) (𝓞 L) := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (fun _ _ h => Subtype.ext ((algebraMap K L).injective (congrArg Subtype.val h)))
  have hj' : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    exact i.injective ((hj a).symm.trans ((congrArg Subtype.val hab).trans (hj b)))
  exact map_differentIdeal_of_span_traceDual
    (R := 𝓞 K) (S := 𝓞 L) (A := A) (B := B) (K := K) (L := L) (F := Fv) (E := E)
    j hj' i (fun a => (hj a).symm)
    (span_globalTraceDual_eq_localizedTraceDual v w A B i e hi hbase htop)

end LocalizedTrace

/-- The actual number-field different extends to the actual different of
the localized complete fields via the original integer embedding. -/
theorem exists_map_differentIdeal_eq_completedDifferent
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
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
    ∃ j : 𝓞 L →+* target.valuationSubring,
      (∀ a : 𝓞 L, (j a : E) = AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (a : L)) ∧
      (finitePlaceExtensionCentre v w).asIdeal.map j = target.maximalIdeal ∧
      target.maximalIdeal.comap j = (finitePlaceExtensionCentre v w).asIdeal ∧
      ramificationIndex base.toDVF target.toDVF =
        v.asIdeal.ramificationIdx' (finitePlaceExtensionCentre v w).asIdeal ∧
      (differentIdeal (𝓞 K) (𝓞 L)).map j =
        RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
          base target := by
  intro vK E algebraOwner finiteOwner abelianOwner valuationOwner localFieldOwner
    base target towerOwner
  classical
  let F := vK.Completion
  let : Algebra.IsSeparable F E := abelianOwner.toIsGalois.to_isSeparable
  let A := base.valuation.valuationSubring
  let B := target.valuation.valuationSubring
  let C := w.1.Completion
  let _ : Algebra B E := Algebra.ofSubsemiring B
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsFractionRing A F := base.toDVF.valuationSubring_isFractionRing
  let : IsFractionRing B E := target.toDVF.valuationSubring_isFractionRing
  let : IsDiscreteValuationRing A := base.toDVF.valuationSubring_isDiscreteValuationRing
  let : IsDiscreteValuationRing B := target.toDVF.valuationSubring_isDiscreteValuationRing
  let : IsIntegralClosure B A E := chosenLocalExtensionCompleteDVF_isIntegralClosure F E
  let : Module.IsTorsionFree A B := moduleIsTorsionFree_target_valuationSubring_of_finite_separable
    (base := base) (target := target)
  let hvK := HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let hvK0 : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let : Algebra F C := AbsoluteValue.completionAlgebra vK w.1 w.2
  let e : E ≃ₐ[F] C := localizedCompletionEquivCompletion vK hvK0 w
  let i : L →+* E := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  have hi (x : L) : e (i x) = AbsoluteValue.toCompletion w.1 x := rfl
  let : ValuativeRel E := localizedCompletionFinitePlaceValuativeRel vK w hvK
  let : base.valuation.HasExtension (ValuativeRel.valuation E) :=
    localizedCompletionValuationHasExtension vK w hvK
  let huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
      base.toDVF target.toDVF := chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension F E
  have hB : B = (ValuativeRel.valuation E).valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mp (huniq (ValuativeRel.valuation E))
  have hbase (x : F) : x ∈ A ↔ x ∈ absoluteValueCompletionIntegers vK hvK := by
    rw [mem_absoluteValueCompletionIntegers_iff]
    exact finitePlaceCompletion_mem_integers_iff_norm_le_one vK hvK x
  have htop (x : E) : x ∈ B ↔ e x ∈ absoluteValueCompletionIntegers w.1
      (absoluteValueExtension_isNonarchimedean vK hvK w) := by
    rw [hB, mem_absoluteValueCompletionIntegers_iff]
    exact localizedCompletion_mem_integers_iff_norm_le_one vK w hvK x
  obtain ⟨j, hj, hP, hPback⟩ := exists_map_comap_localizedPrime v w B i e hi htop
  let P := finitePlaceExtensionCentre v w
  let b : A →+* B := integerMap base.toDVF target.toDVF
  have hpow := maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex base target
  have hram := ramificationIndex_eq_of_localizedIntegerMap v w base B P i e j b
    hj (fun _ => rfl) hi hbase hP hPback
    (ramificationIndex base.toDVF target.toDVF) hpow
  refine ⟨j, hj, hP, hPback, hram, ?_⟩
  exact (map_globalDifferent_eq_localDifferent v w A B i e j hi hj hbase htop).trans
    (differentIdealOfFiniteSeparable_eq_differentIdeal base target).symm

end GlobalClassFieldTheory.GlobalClassFields
