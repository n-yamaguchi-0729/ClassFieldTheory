/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.FinitePlaceHilbertBadSet
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertFamilyAlgEquiv
public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingProperties
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.Core
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation

/-!
# An explicit support bound for every local Hilbert-pairing family

The norm-residue criterion determines the zero set of every such family,
even though it does not determine all of its nontrivial values.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- The finite-place factors of a locally Hilbert family are trivial
where the exponent and both arguments are valuation-ring units. -/
private theorem globalHilbertPairing_mulSupport_subset_finitePlaceHilbertBadSet_native
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n)
    (hB : GlobalHilbertPairingFamily.IsLocallyHilbert F B)
    (a b : Fˣ) :
    Function.mulSupport
        (fun v : HeightOneSpectrum (𝓞 F) =>
          GlobalHilbertPairingFamily.finiteFactor F B hmu v a b) ⊆
      finitePlaceHilbertBadSet F n a b := by
  intro v hv
  by_contra hvBad
  change ¬ (v.valuation F (a : F) ≠ 1 ∨
    v.valuation F (b : F) ≠ 1 ∨
    v.valuation F ((n : ℕ) : F) ≠ 1) at hvBad
  have hva : v.valuation F (a : F) = 1 := by
    by_contra h
    exact hvBad (Or.inl h)
  have hvb : v.valuation F (b : F) = 1 := by
    by_contra h
    exact hvBad (Or.inr (Or.inl h))
  have hvn : v.valuation F ((n : ℕ) : F) = 1 := by
    by_contra h
    exact hvBad (Or.inr (Or.inr h))
  let C := finitePlaceAdicHilbertPairingFamily F n hmu
  have hC : GlobalHilbertPairingFamily.IsLocallyHilbert F C :=
    finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F n hmu
  have hnF : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  have hsource :
      GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        F n hnF hmu v a b = 1 :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
      F n hnF hmu a b v hva hvb hvn
  have hCfactor :
      GlobalHilbertPairingFamily.finiteFactor F C hmu v a b = 1 := by
    rw [finitePlaceAdicHilbertPairingFamily_finiteFactor F n hnF hmu v a b]
    change KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        F n hnF hmu v a b) = 1
    rw [hsource, map_one]
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃*
      rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots
      (algebraMap F (v.adicCompletion F)).injective hmu
  let av : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let bv : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b
  have hzero :
      GlobalHilbertPairingFamily.finiteFactor F C hmu v a b = 1 ↔
        GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1 := by
    change e.symm ((C v).symbol av bv) = 1 ↔
      e.symm ((B v).symbol av bv) = 1
    simp only [MulEquiv.map_eq_one_iff]
    exact ((hC v).2.2.2 av bv).trans ((hB v).2.2.2 av bv).symm
  exact hv (hzero.mp hCfactor)

universe u v

private theorem principalIdele_localOrder_eq_zero_iff
    {F : Type u} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    (FiniteIdeleGroup.localOrder v
      (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F a))).toAdd = 0 ↔
      v.valuation F (a : F) = 1 := by
  rw [FiniteIdeleGroup.localOrder_eq_zero_iff,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
    IdeleGroup.finiteComponent_principalIdele,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

private theorem finitePlaceCongr_valuation_eq_one_iff
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃ₐ[ℚ] G) (W : HeightOneSpectrum (𝓞 G)) (a : Fˣ) :
    W.valuation G ((Units.mapEquiv e.toRingEquiv.toMulEquiv a : Gˣ) : G) = 1 ↔
      ((finitePlaceCongr e).symm W).valuation F (a : F) = 1 := by
  rw [← principalIdele_localOrder_eq_zero_iff,
    ← principalIdele_localOrder_eq_zero_iff]
  have h := ideleCongr_localOrder e (IdeleGroup.principalIdele F a) W
  rw [ideleCongr_principalIdele] at h
  rw [h]

/-- The finite-place factors of any locally Hilbert family are trivial where
its exponent and both arguments are valuation-ring units. The same explicit
bad-place set works in every universe. -/
theorem globalHilbertPairing_mulSupport_subset_finitePlaceHilbertBadSet
    (F : Type u) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n)
    (hB : GlobalHilbertPairingFamily.IsLocallyHilbert F B)
    (a b : Fˣ) :
    Function.mulSupport
        (fun v : HeightOneSpectrum (𝓞 F) =>
          GlobalHilbertPairingFamily.finiteFactor F B hmu v a b) ⊆
      finitePlaceHilbertBadSet F n a b := by
  let : Small.{0} F := numberField_small F
  let S := Shrink.{0} F
  let : NumberField S := numberField_shrink F
  let e : F ≃ₐ[ℚ] S := (Shrink.ringEquiv F).symm.toRatAlgEquiv
  have hmuS : (primitiveRoots (n : ℕ) S).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨e ζ, (mem_primitiveRoots n.pos).2
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective e.injective)⟩
  let BS := globalHilbertPairingFamilyCongr e n hmu B
  have hBS : GlobalHilbertPairingFamily.IsLocallyHilbert S BS :=
    globalHilbertPairingFamilyCongr_isLocallyHilbert e n hmu B hB
  let eu : Fˣ ≃* Sˣ := Units.mapEquiv e.toRingEquiv.toMulEquiv
  let er : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) S :=
    rootsOfUnityEquivOfRingEquiv e.toRingEquiv n hmu
  intro v hv
  by_contra hvBad
  change ¬ (v.valuation F (a : F) ≠ 1 ∨
    v.valuation F (b : F) ≠ 1 ∨
    v.valuation F ((n : ℕ) : F) ≠ 1) at hvBad
  have hva : v.valuation F (a : F) = 1 := by
    by_contra h
    exact hvBad (Or.inl h)
  have hvb : v.valuation F (b : F) = 1 := by
    by_contra h
    exact hvBad (Or.inr (Or.inl h))
  have hvn : v.valuation F ((n : ℕ) : F) = 1 := by
    by_contra h
    exact hvBad (Or.inr (Or.inr h))
  let W := finitePlaceCongr e v
  have hW : (finitePlaceCongr e).symm W = v :=
    (finitePlaceCongr e).symm_apply_apply v
  have hunit (x : Fˣ) (hx : v.valuation F (x : F) = 1) :
      W.valuation S (eu x : S) = 1 := by
    apply (finitePlaceCongr_valuation_eq_one_iff e W x).2
    rw [hW]
    exact hx
  have hvaS := hunit a hva
  have hvbS := hunit b hvb
  have hvnS : W.valuation S ((n : ℕ) : S) = 1 := by
    let nUnit : Fˣ := Units.mk0 ((n : ℕ) : F) (Nat.cast_ne_zero.mpr n.ne_zero)
    have hnUnit := hunit nUnit hvn
    change W.valuation S (e ((n : ℕ) : F)) = 1 at hnUnit
    simpa only [map_natCast] using hnUnit
  have hsmall :
      GlobalHilbertPairingFamily.finiteFactor S BS hmuS W (eu a) (eu b) = 1 := by
    by_contra hne
    have hbad := globalHilbertPairing_mulSupport_subset_finitePlaceHilbertBadSet_native
      S n hmuS BS hBS (eu a) (eu b) hne
    change W.valuation S (eu a : S) ≠ 1 ∨
      W.valuation S (eu b : S) ≠ 1 ∨
      W.valuation S ((n : ℕ) : S) ≠ 1 at hbad
    rcases hbad with ha | hb | hn
    · exact ha hvaS
    · exact hb hvbS
    · exact hn hvnS
  have hvalue := globalHilbertPairingFamilyCongr_finiteFactor e n hmu hmuS B W a b
  rw [hW] at hvalue
  apply hv
  apply er.injective
  calc
    er (GlobalHilbertPairingFamily.finiteFactor F B hmu v a b) =
        GlobalHilbertPairingFamily.finiteFactor S BS hmuS W (eu a) (eu b) := hvalue
    _ = 1 := hsmall
    _ = er 1 := (map_one er).symm

end ClassFieldTheory
