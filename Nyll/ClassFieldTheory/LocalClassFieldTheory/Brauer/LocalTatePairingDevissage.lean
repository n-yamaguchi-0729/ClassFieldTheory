/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateDualExactness
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairingNaturality
public import Nyll.GaloisCohomology.GroupTheory.FinitePGroupInvariants
public import Nyll.GaloisCohomology.Topology.InvariantCoefficientExactness
public import Nyll.GaloisCohomology.Topology.InvariantCoefficientSubrepresentation
public import Nyll.GaloisCohomology.Topology.TrivialIntegralCoefficientLine
public import Mathlib.LinearAlgebra.Quotient.Card

/-! # Dévissage of the degree-one local Tate pairing -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+)

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Mu" => separableMuTopRep K n
local notation "D" A:arg => discreteLinearDual (R := ℤ) (G := Γabs) A Mu
local notation "H" => _root_.continuousCohomology (k := ℤ) (G := Γabs)
local notation "κ" => map (ContinuousMonoidHom.id Γabs)

local instance : LocallyCompactSpace Γabs :=
  inferInstanceAs (LocallyCompactSpace (InfiniteGalois.profiniteGalGrp K (SeparableClosure K)))

/-- The additive adjoint of a biadditive pairing. -/
def pairingAdjoint {A : Type*} {B : Type*} {C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (p : A → B → C) (hA : ∀ a a' b, p (a + a') b = p a b + p a' b)
    (hB : ∀ a b b', p a (b + b') = p a b + p a b') : A →+ (B →+ C) :=
  { toFun := fun a =>
      { toFun := p a
        map_zero' := by
          have h := hB a 0 0
          rw [zero_add] at h
          exact add_eq_left.mp h.symm
        map_add' := hB a }
    map_zero' := by
      apply AddMonoidHom.ext
      intro b
      have h := hA 0 0 b
      rw [zero_add] at h
      exact add_eq_left.mp h.symm
    map_add' := fun a a' => AddMonoidHom.ext fun b => hA a a' b }

/-- The actual degree-zero pairing as an additive homomorphism into the
full character group on opposite degree-two cohomology. -/
def localTatePairingZeroAdjoint (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A]
    (hn : ((n : ℕ) : K) ≠ 0) : H 0 A →+ (H 2 (D A) →+ ZMod (n : ℕ)) :=
  pairingAdjoint (localTatePairingZero K n A hn)
    (fun a a' b => by
      unfold localTatePairingZero
      rw [cupZeroTwo_add_left, map_add])
    (fun a b b' => by
      unfold localTatePairingZero
      rw [cupZeroTwo_add_right, map_add])

/-- The actual cup pairing, with trace, as an additive map into the full
character group on opposite degree-one cohomology. -/
def localTatePairingOneAdjoint (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A]
    (hn : ((n : ℕ) : K) ≠ 0) : H 1 A →+ (H 1 (D A) →+ ZMod (n : ℕ)) :=
  pairingAdjoint (localTatePairingOne K n A hn)
    (localTatePairingOne_add_left K n A hn) (localTatePairingOne_add_right K n A hn)

/-- The actual degree-two pairing as an additive homomorphism into the
full character group on the invariant dual coefficients. -/
def localTatePairingTwoAdjoint (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A]
    (hn : ((n : ℕ) : K) ≠ 0) : H 2 A →+ (H 0 (D A) →+ ZMod (n : ℕ)) :=
  pairingAdjoint (localTatePairingTwo K n A hn)
    (fun a a' b => by
      unfold localTatePairingTwo
      rw [cupTwoZero_add_left, map_add])
    (fun a b b' => by
      unfold localTatePairingTwo
      rw [cupTwoZero_add_right, map_add])

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localTateDualCohomology_annihilated
    (A : TopRep.{u} ℤ Γabs) (i : ℕ) (x : H i (D A)) : (n : ℕ) • x = 0 :=
  nsmul_continuousCohomology_eq_zero_of_coefficients (D A) n
    (separableMu_dual_nsmul_eq_zero K n A) i x

private theorem localTatePairingTwo_zero_left (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A]
    (hn : ((n : ℕ) : K) ≠ 0) (y : H 0 (D A)) : localTatePairingTwo K n A hn 0 y = 0 := by
  unfold localTatePairingTwo cupTwoZero
  rw [map_zero, map_zero]

private theorem exists_leftAdjoint_lift {A B A' B' C' : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    {m : ℕ} [NeZero m]
    (F : A →+ (A' →+ ZMod m)) (M : B →+ (B' →+ ZMod m))
    (f : A →+ B) (f' : B' →+ A') (g' : C' →+ B')
    (hF : Function.Surjective F) (hann : ∀ a' : A', m • a' = 0)
    (hexact : ∀ y : B', f' y = 0 → ∃ z : C', g' z = y)
    (hadj : ∀ a y, M (f a) y = F a (f' y))
    (b : B) (targetCharacter : B' →+ ZMod m) (hb : ∀ z : C', M b (g' z) = targetCharacter (g' z)) :
    ∃ b' : B, M b' = targetCharacter := by
  let l := targetCharacter - M b
  obtain ⟨φ, hφ⟩ := exists_addHom_zmod_extension_of_ker_le m f' l (by
    intro y hy
    obtain ⟨z, hz⟩ := hexact y hy
    change targetCharacter y - M b y = 0
    rw [← hz, hb, sub_self]) hann
  obtain ⟨a, ha⟩ := hF φ
  refine ⟨b + f a, ?_⟩
  rw [map_add]
  ext y
  change M b y + M (f a) y = targetCharacter y
  rw [hadj, ha]
  have hy := DFunLike.congr_fun hφ y
  change φ (f' y) = targetCharacter y - M b y at hy
  rw [hy]
  abel

/-- The five-term segment of the actual long exact sequence and its dual
transfers degree-one perfectness to the middle coefficients. The two
adjacent boundary comparisons use the signed continuous cup identities. -/
theorem localTatePairingOneAdjoint_bijective_of_shortExact
    (hn : ((n : ℕ) : K) ≠ 0) (S : ShortComplex (TopRep.{u} ℤ Γabs))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hD : ((discreteLinearDualShortComplex Mu S).map
      (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hA₁ : Function.Bijective (localTatePairingOneAdjoint K n S.X₁ hn))
    (hC₁ : Function.Bijective (localTatePairingOneAdjoint K n S.X₃ hn))
    (hA₂ : Function.Injective (localTatePairingTwo K n S.X₁ hn))
    (hC₀ : ∀ φ : H 2 (D S.X₃) →+ ZMod (n : ℕ),
      ∃ c : H 0 S.X₃, ∀ y : H 2 (D S.X₃), localTatePairingZero K n S.X₃ hn c y = φ y) :
    Function.Bijective (localTatePairingOneAdjoint K n S.X₂ hn) := by
  let A := S.X₁
  let B := S.X₂
  let C := S.X₃
  let T := discreteLinearDualShortComplex Mu S
  let F := localTatePairingOneAdjoint K n A hn
  let M := localTatePairingOneAdjoint K n B hn
  let E := localTatePairingOneAdjoint K n C hn
  let f : H 1 A →+ H 1 B := (κ S.f 1).hom.toLinearMap.toAddMonoidHom
  let g : H 1 B →+ H 1 C := (κ S.g 1).hom.toLinearMap.toAddMonoidHom
  let fD : H 1 (D B) →+ H 1 (D A) := (κ T.g 1).hom.toLinearMap.toAddMonoidHom
  let gD : H 1 (D C) →+ H 1 (D B) := (κ T.f 1).hom.toLinearMap.toAddMonoidHom
  let δD := discreteCoefficientConnecting T hD 1
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hf (a : H 1 A) (y : H 1 (D B)) : M (f a) y = F a (fD y) :=
    localTatePairingOne_coefficientMap K n S.f hn a y
  have hg (b : H 1 B) (y : H 1 (D C)) : E (g b) y = M b (gD y) :=
    localTatePairingOne_coefficientMap K n S.g hn b y
  constructor
  · apply (injective_iff_map_eq_zero M).mpr
    intro b hb
    have hgzero : E (g b) = 0 := by
      ext y
      exact (hg b y).trans (DFunLike.congr_fun hb (gD y))
    have hgb : g b = 0 := (injective_iff_map_eq_zero E).mp hC₁.injective _ hgzero
    obtain ⟨a, ha⟩ := exists_continuousCohomology_preimage_of_map_eq_zero S hS 1 b hgb
    change f a = b at ha
    obtain ⟨φ, hφ⟩ := exists_addHom_zmod_extension_of_ker_le n δD (F a) (by
      intro y hy
      obtain ⟨z, hz⟩ := exists_continuousCohomology_preimage_of_connecting_eq_zero T hD 1 y hy
      change F a y = 0
      change fD z = y at hz
      calc
        F a y = F a (fD z) := congrArg (F a) hz.symm
        _ = M (f a) z := (hf a z).symm
        _ = M b z := congrArg (fun t => M t z) ha
        _ = 0 := DFunLike.congr_fun hb z) (localTateDualCohomology_annihilated K n C 2)
    obtain ⟨c, hc⟩ := hC₀ (-φ)
    have hac : discreteCoefficientConnecting S hS 0 c = a := by
      apply hA₁.injective
      ext y
      change localTatePairingOne K n A hn (discreteCoefficientConnecting S hS 0 c) y = F a y
      rw [localTatePairing_connectingZero K n hn S hS hD]
      let z := δD y
      change -localTatePairingZero K n C hn c z = F a y
      calc
        _ = -((-φ) z) := congrArg Neg.neg (hc z)
        _ = φ z := neg_neg _
        _ = _ := DFunLike.congr_fun hφ y
    rw [← ha, ← hac]
    exact continuousCohomology_map_connecting_eq_zero S hS 0 c
  · intro targetCharacter
    obtain ⟨c, hc⟩ := hC₁.surjective (targetCharacter.comp gD)
    have hδ : discreteCoefficientConnecting S hS 1 c = 0 := by
      apply hA₂
      funext y
      rw [localTatePairing_connectingOne K n hn S hS hD, localTatePairingTwo_zero_left]
      change E c (discreteCoefficientConnecting T hD 0 y) = 0
      rw [hc]
      change targetCharacter ((κ T.f 1) (discreteCoefficientConnecting T hD 0 y)) = 0
      have hzero : (κ T.f 1) (discreteCoefficientConnecting T hD 0 y) = 0 :=
        continuousCohomology_map_connecting_eq_zero T hD 0 y
      exact (congrArg targetCharacter hzero).trans (map_zero targetCharacter)
    obtain ⟨b, hb⟩ := exists_continuousCohomology_preimage_of_connecting_eq_zero S hS 1 c hδ
    change g b = c at hb
    refine exists_leftAdjoint_lift F M f fD gD hA₁.surjective
      (localTateDualCohomology_annihilated K n A 1)
      (exists_continuousCohomology_preimage_of_map_eq_zero T hD 1) hf b targetCharacter ?_
    intro y
    exact (hg b y).symm.trans
      ((congrArg (fun t => E t y) hb).trans (DFunLike.congr_fun hc y))

/-- Degree-zero perfectness passes through a short exact sequence when
degree three of the opposite end dual vanishes. -/
theorem localTatePairingZeroAdjoint_bijective_of_shortExact
    (hn : ((n : ℕ) : K) ≠ 0) (S : ShortComplex (TopRep.{u} ℤ Γabs))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hD : ((discreteLinearDualShortComplex Mu S).map
      (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hA₀ : Function.Bijective (localTatePairingZeroAdjoint K n S.X₁ hn))
    (hC₀ : Function.Bijective (localTatePairingZeroAdjoint K n S.X₃ hn))
    (hA₁ : Function.Injective (localTatePairingOneAdjoint K n S.X₁ hn))
    (hC₃ : ∀ y : H 3 (D S.X₃), y = 0) :
    Function.Bijective (localTatePairingZeroAdjoint K n S.X₂ hn) := by
  let A := S.X₁
  let B := S.X₂
  let C := S.X₃
  let T := discreteLinearDualShortComplex Mu S
  let F := localTatePairingZeroAdjoint K n A hn
  let M := localTatePairingZeroAdjoint K n B hn
  let E := localTatePairingZeroAdjoint K n C hn
  let f : H 0 A →+ H 0 B := (κ S.f 0).hom.toLinearMap.toAddMonoidHom
  let g : H 0 B →+ H 0 C := (κ S.g 0).hom.toLinearMap.toAddMonoidHom
  let fD : H 2 (D B) →+ H 2 (D A) := (κ T.g 2).hom.toLinearMap.toAddMonoidHom
  let gD : H 2 (D C) →+ H 2 (D B) := (κ T.f 2).hom.toLinearMap.toAddMonoidHom
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hf (a : H 0 A) (y : H 2 (D B)) : M (f a) y = F a (fD y) :=
    localTatePairingZero_coefficientMap K n S.f hn a y
  have hg (b : H 0 B) (y : H 2 (D C)) : E (g b) y = M b (gD y) :=
    localTatePairingZero_coefficientMap K n S.g hn b y
  constructor
  · apply (injective_iff_map_eq_zero M).mpr
    intro b hb
    have hgb : g b = 0 := by
      apply (injective_iff_map_eq_zero E).mp hC₀.injective
      ext y
      exact (hg b y).trans (DFunLike.congr_fun hb (gD y))
    obtain ⟨a, ha⟩ := exists_continuousCohomology_preimage_of_map_eq_zero S hS 0 b hgb
    change f a = b at ha
    have ha₀ : a = 0 := by
      apply (injective_iff_map_eq_zero F).mp hA₀.injective
      ext y
      obtain ⟨z, hz⟩ := exists_continuousCohomology_preimage_of_connecting_eq_zero T hD 2 y
        (hC₃ (discreteCoefficientConnecting T hD 2 y))
      change fD z = y at hz
      change F a y = 0
      calc
        _ = F a (fD z) := congrArg (F a) hz.symm
        _ = M (f a) z := (hf a z).symm
        _ = M b z := congrArg (fun t => M t z) ha
        _ = 0 := DFunLike.congr_fun hb z
    rw [← ha, ha₀, map_zero]
  · intro targetCharacter
    obtain ⟨c, hc⟩ := hC₀.surjective (targetCharacter.comp gD)
    have hδ : discreteCoefficientConnecting S hS 0 c = 0 := by
      apply (injective_iff_map_eq_zero (localTatePairingOneAdjoint K n A hn)).mp hA₁
      ext y
      change localTatePairingOne K n A hn (discreteCoefficientConnecting S hS 0 c) y = 0
      rw [localTatePairing_connectingZero K n hn S hS hD]
      change -(E c (discreteCoefficientConnecting T hD 1 y)) = 0
      rw [hc]
      change -targetCharacter ((κ T.f 2) (discreteCoefficientConnecting T hD 1 y)) = 0
      have hzero : (κ T.f 2) (discreteCoefficientConnecting T hD 1 y) = 0 :=
        continuousCohomology_map_connecting_eq_zero T hD 1 y
      exact (congrArg (fun z => -targetCharacter z) hzero).trans
        ((congrArg Neg.neg (map_zero targetCharacter)).trans neg_zero)
    obtain ⟨b, hb⟩ := exists_continuousCohomology_preimage_of_connecting_eq_zero S hS 0 c hδ
    change g b = c at hb
    refine exists_leftAdjoint_lift F M f fD gD hA₀.surjective
      (localTateDualCohomology_annihilated K n A 2)
      (exists_continuousCohomology_preimage_of_map_eq_zero T hD 2) hf b targetCharacter ?_
    intro y
    exact (hg b y).symm.trans
      ((congrArg (fun t => E t y) hb).trans (DFunLike.congr_fun hc y))

/-- Degree-two perfectness passes through a short exact sequence when
degree three of the left coefficient vanishes. -/
theorem localTatePairingTwoAdjoint_bijective_of_shortExact
    (hn : ((n : ℕ) : K) ≠ 0) (S : ShortComplex (TopRep.{u} ℤ Γabs))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hD : ((discreteLinearDualShortComplex Mu S).map
      (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hA₂ : Function.Bijective (localTatePairingTwoAdjoint K n S.X₁ hn))
    (hC₂ : Function.Bijective (localTatePairingTwoAdjoint K n S.X₃ hn))
    (hC₁ : Function.Surjective (localTatePairingOneAdjoint K n S.X₃ hn))
    (hA₃ : ∀ x : H 3 S.X₁, x = 0) :
    Function.Bijective (localTatePairingTwoAdjoint K n S.X₂ hn) := by
  let A := S.X₁
  let B := S.X₂
  let C := S.X₃
  let T := discreteLinearDualShortComplex Mu S
  let F := localTatePairingTwoAdjoint K n A hn
  let M := localTatePairingTwoAdjoint K n B hn
  let E := localTatePairingTwoAdjoint K n C hn
  let f : H 2 A →+ H 2 B := (κ S.f 2).hom.toLinearMap.toAddMonoidHom
  let g : H 2 B →+ H 2 C := (κ S.g 2).hom.toLinearMap.toAddMonoidHom
  let fD : H 0 (D B) →+ H 0 (D A) := (κ T.g 0).hom.toLinearMap.toAddMonoidHom
  let gD : H 0 (D C) →+ H 0 (D B) := (κ T.f 0).hom.toLinearMap.toAddMonoidHom
  let δD := discreteCoefficientConnecting T hD 0
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hf (a : H 2 A) (y : H 0 (D B)) : M (f a) y = F a (fD y) :=
    localTatePairingTwo_coefficientMap K n S.f hn a y
  have hg (b : H 2 B) (y : H 0 (D C)) : E (g b) y = M b (gD y) :=
    localTatePairingTwo_coefficientMap K n S.g hn b y
  constructor
  · apply (injective_iff_map_eq_zero M).mpr
    intro b hb
    have hgb : g b = 0 := by
      apply (injective_iff_map_eq_zero E).mp hC₂.injective
      ext y
      exact (hg b y).trans (DFunLike.congr_fun hb (gD y))
    obtain ⟨a, ha⟩ := exists_continuousCohomology_preimage_of_map_eq_zero S hS 2 b hgb
    change f a = b at ha
    obtain ⟨φ, hφ⟩ := exists_addHom_zmod_extension_of_ker_le n δD (F a) (by
      intro y hy
      obtain ⟨z, hz⟩ := exists_continuousCohomology_preimage_of_connecting_eq_zero T hD 0 y hy
      change fD z = y at hz
      change F a y = 0
      calc
        F a y = F a (fD z) := congrArg (F a) hz.symm
        _ = M (f a) z := (hf a z).symm
        _ = M b z := congrArg (fun t => M t z) ha
        _ = 0 := DFunLike.congr_fun hb z) (localTateDualCohomology_annihilated K n C 1)
    obtain ⟨c, hc⟩ := hC₁ φ
    have hac : discreteCoefficientConnecting S hS 1 c = a := by
      apply hA₂.injective
      ext y
      change localTatePairingTwo K n A hn (discreteCoefficientConnecting S hS 1 c) y = F a y
      rw [localTatePairing_connectingOne K n hn S hS hD]
      change localTatePairingOneAdjoint K n C hn c (δD y) = F a y
      rw [hc]
      exact DFunLike.congr_fun hφ y
    rw [← ha, ← hac]
    exact continuousCohomology_map_connecting_eq_zero S hS 1 c
  · intro targetCharacter
    obtain ⟨c, hc⟩ := hC₂.surjective (targetCharacter.comp gD)
    obtain ⟨b, hb⟩ := exists_continuousCohomology_preimage_of_connecting_eq_zero S hS 2 c
      (hA₃ (discreteCoefficientConnecting S hS 2 c))
    change g b = c at hb
    refine exists_leftAdjoint_lift F M f fD gD hA₂.surjective
      (localTateDualCohomology_annihilated K n A 0)
      (exists_continuousCohomology_preimage_of_map_eq_zero T hD 0) hf b targetCharacter ?_
    intro y
    exact (hg b y).symm.trans
      ((congrArg (fun t => E t y) hb).trans (DFunLike.congr_fun hc y))

/-- Once degree three vanishes at the two ends needed by the long exact
sequences, all three actual local pairings pass through the same short
exact coefficient sequence. -/
theorem localTatePairingAdjoints_bijective_of_shortExact
    (hn : ((n : ℕ) : K) ≠ 0) (S : ShortComplex (TopRep.{u} ℤ Γabs))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hD : ((discreteLinearDualShortComplex Mu S).map
      (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hA : Function.Bijective (localTatePairingZeroAdjoint K n S.X₁ hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n S.X₁ hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n S.X₁ hn))
    (hC : Function.Bijective (localTatePairingZeroAdjoint K n S.X₃ hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n S.X₃ hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n S.X₃ hn))
    (hA₃ : ∀ x : H 3 S.X₁, x = 0) (hC₃ : ∀ y : H 3 (D S.X₃), y = 0) :
    Function.Bijective (localTatePairingZeroAdjoint K n S.X₂ hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n S.X₂ hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n S.X₂ hn) := by
  refine ⟨
    localTatePairingZeroAdjoint_bijective_of_shortExact K n hn S hS hD
      hA.1 hC.1 hA.2.1.injective hC₃,
    localTatePairingOneAdjoint_bijective_of_shortExact K n hn S hS hD hA.2.1 hC.2.1 ?_ ?_,
    localTatePairingTwoAdjoint_bijective_of_shortExact K n hn S hS hD
      hA.2.2 hC.2.2 hC.2.1.surjective hA₃⟩
  · intro a b h
    apply hA.2.2.injective
    ext y
    exact congrFun h y
  · intro φ
    obtain ⟨c, hc⟩ := hC.1.surjective φ
    exact ⟨c, fun y => DFunLike.congr_fun hc y⟩

local notation "Perfect(" A "," hn ")" =>
  (Function.Bijective (localTatePairingZeroAdjoint K n A hn) ∧
    Function.Bijective (localTatePairingOneAdjoint K n A hn) ∧
    Function.Bijective (localTatePairingTwoAdjoint K n A hn))

private theorem adjoint_bijective_of_zero {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ (B →+ ZMod (n : ℕ))) (hA : ∀ a : A, a = 0) (hB : ∀ b : B, b = 0) :
    Function.Bijective f := by
  refine ⟨fun a b _ => (hA a).trans (hA b).symm, fun φ => ⟨0, ?_⟩⟩
  ext b
  simp only [hB b, map_zero]

private theorem localTatePairingAdjoints_bijective_of_trivial_coefficients
    (hn : ((n : ℕ) : K) ≠ 0) (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A] [Subsingleton A] :
    Perfect(A, hn) := by
  let : Module ℤ A := A.hV2
  let : Module ℤ Mu := (separableMuTopRep K n).hV2
  let : Subsingleton (D A) := ⟨fun f g => by
    change discreteLinearDualMap A Mu f = discreteLinearDualMap A Mu g
    apply LinearMap.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    exact ((congrArg (discreteLinearDualMap A Mu f) ha).trans (map_zero _)).trans
      ((congrArg (discreteLinearDualMap A Mu g) ha).trans (map_zero _)).symm⟩
  have hzero (V : TopRep.{u} ℤ Γabs) [Subsingleton V] (i : ℕ) (x : H i V) : x = 0 :=
    cohomology_eq_zero_of_continuousModuleComplex_isZero Γabs V i
      (continuousModuleHomology_isZero_of_subsingleton Γabs V i) x
  exact ⟨adjoint_bijective_of_zero n _ (hzero A 0) (hzero (D A) 2),
    adjoint_bijective_of_zero n _ (hzero A 1) (hzero (D A) 1),
    adjoint_bijective_of_zero n _ (hzero A 2) (hzero (D A) 0)⟩

private theorem nsmul_zero_of_annihilator_dvd {B : Type u} [AddCommGroup B]
    {m m' : ℕ} (h : m ∣ m') {x : B} (hx : m • x = 0) : m' • x = 0 := by
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp ((addOrderOf_dvd_iff_nsmul_eq_zero.mpr hx).trans h)

/-- For a fixed étale dualizing coefficient, the actual local pairings for
finite discrete torsion follow from their prime-annihilated cases and
degree-three vanishing. The induction uses the original invariant
subrepresentation and its actual quotient. -/
theorem localTatePairingAdjoints_bijective_of_prime_coefficients
    (hn : ((n : ℕ) : K) ≠ 0)
    (h₃ : ∀ (A : TopRep.{u} ℤ Γabs) [Finite A] [DiscreteTopology A],
      Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2) →
      (∀ a : A, (n : ℕ) • a = 0) → ∀ x : H 3 A, x = 0)
    (hprime : ∀ (p : ℕ), p.Prime → p ∣ (n : ℕ) →
      ∀ (A : TopRep.{u} ℤ Γabs) [Finite A] [DiscreteTopology A],
        Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2) → (∀ a : A, p • a = 0) → Perfect(A, hn))
    (X : TopRep.{u} ℤ Γabs) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Γabs × X => X.ρ gx.1 gx.2)) (hXn : ∀ x : X, (n : ℕ) • x = 0) :
    Perfect(X, hn) := by
  classical
  suffices step : ∀ m : ℕ, 0 < m → m ∣ (n : ℕ) →
      ∀ (Y : TopRep.{u} ℤ Γabs) [Finite Y] [DiscreteTopology Y],
        Continuous (fun gy : Γabs × Y => Y.ρ gy.1 gy.2) → (∀ y : Y, m • y = 0) → Perfect(Y, hn) by
    exact step n n.pos dvd_rfl X hX hXn
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm hmn Y hfin hdisc hY hmY
    by_cases hm1 : m = 1
    · let : Subsingleton Y := ⟨fun y z => by
        have hzero (w : Y) : w = 0 := by simpa only [hm1, one_nsmul] using hmY w
        exact (hzero y).trans (hzero z).symm⟩
      exact localTatePairingAdjoints_bijective_of_trivial_coefficients K n hn Y
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hm1
      let : Module ℤ Y := Y.hV2
      let W : Submodule ℤ Y := LinearMap.ker (p • (LinearMap.id : Y →ₗ[ℤ] Y))
      have hW (g : Γabs) : W ≤ W.comap (Y.ρ g).toLinearMap := by
        intro y hy
        change p • y = 0 at hy
        change p • Y.ρ g y = 0
        rw [← map_nsmul, hy, map_zero]
      let A := invariantSubmoduleTopRep ℤ Γabs Y W hW
      let : Module ℤ A := A.hV2
      let f : A ⟶ Y := invariantSubmoduleInclusion ℤ Γabs Y W hW
      let I := LinearMap.range f.hom.toContinuousLinearMap.toLinearMap
      let hI := coefficientMapRange_invariant ℤ Γabs A Y f
      let Q := invariantCoefficientQuotient ℤ Γabs Y I hI
      let S := coefficientRangeShortComplex ℤ Γabs A Y f
      let : Finite A := inferInstanceAs (Finite W)
      let : DiscreteTopology A := invariantSubmoduleTopRep_discrete ℤ Γabs Y W hW
      let : Finite Q := Finite.of_surjective (invariantCoefficientQuotientProjection ℤ Γabs Y I hI)
        (invariantCoefficientQuotientProjection_surjective ℤ Γabs Y I hI)
      let : DiscreteTopology Q := invariantCoefficientQuotient_discrete ℤ Γabs Y I hI
      have hA := invariantSubmoduleTopRep_action_continuous ℤ Γabs Y W hW hY
      have hQ := invariantCoefficientQuotient_action_continuous ℤ Γabs Y I hI hY
      have hpA (a : A) : p • a = 0 := Subtype.ext a.property
      have hmQ (q : Q) : (m / p) • q = 0 := by
        obtain ⟨y, rfl⟩ := invariantCoefficientQuotientProjection_surjective ℤ Γabs Y I hI q
        rw [← map_nsmul]
        apply (invariantCoefficientQuotientProjection_eq_zero_iff ℤ Γabs Y I hI _).mpr
        have hy : (m / p) • y ∈ W := by
          change p • ((m / p) • y) = 0
          rw [← mul_nsmul, Nat.div_mul_cancel hpd]
          exact hmY y
        exact ⟨⟨(m / p) • y, hy⟩, rfl⟩
      have hdvd : m / p ∣ (n : ℕ) := (Nat.div_dvd_of_dvd hpd).trans hmn
      have hlt : m / p < m := Nat.div_lt_self hm hp.one_lt
      have hpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpd) hp.pos
      have hf : Function.Injective f := invariantSubmoduleInclusion_injective ℤ Γabs Y W hW
      have hg : Function.Surjective S.g :=
        invariantCoefficientQuotientProjection_surjective ℤ Γabs Y I hI
      have hexact (y : Y) (hy : S.g y = 0) : ∃ a : A, S.f a = y :=
        (invariantCoefficientQuotientProjection_eq_zero_iff ℤ Γabs Y I hI y).mp hy
      let : Finite S.X₂ := (inferInstance : Finite Y)
      let : Finite S.X₃ := (inferInstance : Finite Q)
      let : DiscreteTopology S.X₁ := (inferInstance : DiscreteTopology A)
      let : DiscreteTopology S.X₂ := (inferInstance : DiscreteTopology Y)
      let : DiscreteTopology S.X₃ := (inferInstance : DiscreteTopology Q)
      have hS := coefficientRangeContinuousModule_shortExact Γabs A Y f hf hA hY
      have hD := separableMu_dualContinuousModuleComplex_shortExact K n hn S hf hg hexact
        (fun y => nsmul_zero_of_annihilator_dvd hmn (hmY y)) hY hQ
      let : Finite Mu := separableMuTopRep_finite K n hn
      let : Finite (D Q) := discreteLinearDual_finite Q Mu
      have hDQ :=
        discreteLinearDual_action_continuous Q Mu hQ (separableMuTopRep_action_continuous K n)
      exact localTatePairingAdjoints_bijective_of_shortExact K n hn S hS hD
        (hprime p hp (hpd.trans hmn) A hA hpA) (ih (m / p) hlt hpos hdvd Q hQ hmQ)
        (h₃ A hA (fun a => nsmul_zero_of_annihilator_dvd (hpd.trans hmn) (hpA a)))
        (h₃ (D Q) hDQ (separableMu_dual_nsmul_eq_zero K n Q))

/-- On prime-annihilated coefficients with p-group action image, perfectness
reduces to the actual trivial `ZMod p` line. Each step takes the quotient by
an invariant line obtained from the original representation. -/
theorem localTatePairingAdjoints_bijective_of_pGroup_image
    (hn : ((n : ℕ) : K) ≠ 0) (p : ℕ) [Fact p.Prime] (hpn : p ∣ (n : ℕ))
    (h₃ : ∀ (A : TopRep.{u} ℤ Γabs) [Finite A] [DiscreteTopology A],
      Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2) →
      (∀ a : A, (n : ℕ) • a = 0) → ∀ x : H 3 A, x = 0)
    (htriv : let T := ClassFieldTower.Cohomology.trivialIntegralZModPLifted p Γabs
      letI : DiscreteTopology T := inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))
      Perfect(T, hn))
    (X : TopRep.{u} ℤ Γabs) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Γabs × X => X.ρ gx.1 gx.2)) (hpX : ∀ x : X, p • x = 0)
    (hρ : let _ : Module ℤ X := X.hV2
      IsPGroup p X.ρ.toRepresentation.asGroupHom.range) : Perfect(X, hn) := by
  classical
  let T := ClassFieldTower.Cohomology.trivialIntegralZModPLifted p Γabs
  let : Finite T := inferInstanceAs (Finite (ULift.{u} (ZMod p)))
  let : DiscreteTopology T := inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))
  have hT : Continuous (fun gt : Γabs × T => T.ρ gt.1 gt.2) := continuous_snd
  suffices step : ∀ m : ℕ,
      ∀ (Y : TopRep.{u} ℤ Γabs) [Finite Y] [DiscreteTopology Y], Nat.card Y = m →
        Continuous (fun gy : Γabs × Y => Y.ρ gy.1 gy.2) → (∀ y : Y, p • y = 0) →
        (let _ : Module ℤ Y := Y.hV2
         IsPGroup p Y.ρ.toRepresentation.asGroupHom.range) → Perfect(Y, hn) by
    exact step (Nat.card X) X rfl hX hpX hρ
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro Y hfin hdisc hcard hY hpY hρY
    cases subsingleton_or_nontrivial Y with
    | inl hzero =>
      let : Subsingleton Y := hzero
      exact localTatePairingAdjoints_bijective_of_trivial_coefficients K n hn Y
    | inr hnontriv =>
      let : Nontrivial Y := hnontriv
      let : Module ℤ Y := Y.hV2
      obtain ⟨v, hv, hfix⟩ := Representation.exists_nonzero_fixed_of_image_isPGroup_int
        Y.ρ.toRepresentation hρY hpY
      let f : T ⟶ Y := trivialIntegralCoefficientLineHom Γabs Y p v (hpY v) hfix
      have hf : Function.Injective f :=
        trivialIntegralCoefficientLineHom_injective Γabs Y p v (hpY v) hfix hv
      let W := LinearMap.range f.hom.toContinuousLinearMap.toLinearMap
      let hW := coefficientMapRange_invariant ℤ Γabs T Y f
      let Q := invariantCoefficientQuotient ℤ Γabs Y W hW
      let S := coefficientRangeShortComplex ℤ Γabs T Y f
      let : Finite Q := Finite.of_surjective (invariantCoefficientQuotientProjection ℤ Γabs Y W hW)
        (invariantCoefficientQuotientProjection_surjective ℤ Γabs Y W hW)
      let : DiscreteTopology Q := invariantCoefficientQuotient_discrete ℤ Γabs Y W hW
      have hQ := invariantCoefficientQuotient_action_continuous ℤ Γabs Y W hW hY
      have hpQ (q : Q) : p • q = 0 := by
        obtain ⟨y, rfl⟩ := invariantCoefficientQuotientProjection_surjective ℤ Γabs Y W hW q
        rw [← map_nsmul, hpY, map_zero]
      let : Module ℤ Q := Q.hV2
      have hρQ : IsPGroup p Q.ρ.toRepresentation.asGroupHom.range :=
        Representation.isPGroup_quotient_image Y.ρ.toRepresentation W hW hρY
      have : Nontrivial W := by
        apply nontrivial_of_ne (⟨f (ULift.up (1 : ZMod p)), ⟨_, rfl⟩⟩ : W) 0
        intro heq
        have hz : f (ULift.up (1 : ZMod p)) = f 0 :=
          (congrArg Subtype.val heq).trans (map_zero f.hom).symm
        exact one_ne_zero (congrArg ULift.down (hf hz))
      let : Fintype W := Fintype.ofFinite W
      have hWcard : 1 < Nat.card W := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      have hQpos : 0 < Nat.card Q := Nat.card_pos
      have hlt : Nat.card Q < m := by
        rw [← hcard]
        change 0 < Nat.card (Y ⧸ W) at hQpos
        change Nat.card (Y ⧸ W) < Nat.card Y
        rw [W.card_eq_card_quotient_mul_card]
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hWcard hQpos
      have hYn (y : Y) : (n : ℕ) • y = 0 := nsmul_zero_of_annihilator_dvd hpn (hpY y)
      have hTn (t : T) : (n : ℕ) • t = 0 := by
        apply hf
        rw [map_nsmul, hYn, map_zero]
      have hg : Function.Surjective S.g :=
        invariantCoefficientQuotientProjection_surjective ℤ Γabs Y W hW
      have hexact (y : Y) (hy : S.g y = 0) : ∃ a : T, S.f a = y :=
        (invariantCoefficientQuotientProjection_eq_zero_iff ℤ Γabs Y W hW y).mp hy
      let : Finite S.X₂ := (inferInstance : Finite Y)
      let : Finite S.X₃ := (inferInstance : Finite Q)
      let : DiscreteTopology S.X₁ := (inferInstance : DiscreteTopology T)
      let : DiscreteTopology S.X₂ := (inferInstance : DiscreteTopology Y)
      let : DiscreteTopology S.X₃ := (inferInstance : DiscreteTopology Q)
      have hS := coefficientRangeContinuousModule_shortExact Γabs T Y f hf hT hY
      have hD := separableMu_dualContinuousModuleComplex_shortExact K n hn S hf hg hexact hYn hY hQ
      let : Finite Mu := separableMuTopRep_finite K n hn
      let : Finite (D Q) := discreteLinearDual_finite Q Mu
      have hDQ :=
        discreteLinearDual_action_continuous Q Mu hQ (separableMuTopRep_action_continuous K n)
      exact localTatePairingAdjoints_bijective_of_shortExact K n hn S hS hD htriv
        (ih (Nat.card Q) hlt Q rfl hQ hpQ hρQ) (h₃ T hT hTn)
        (h₃ (D Q) hDQ (separableMu_dual_nsmul_eq_zero K n Q))

end ClassFieldTheory.Brauer
