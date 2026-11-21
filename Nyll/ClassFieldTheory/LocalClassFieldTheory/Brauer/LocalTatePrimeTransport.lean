/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.EmbeddedKummerTrace
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalCohomologicalDimension
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairingDevissage
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePrimeTarget
public import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv

/-! # Transport of the local Tate pairings through embedded fields and open subgroups -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ContinuousCohomology LocalFieldTheory TopRep

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+)

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Mu" => separableMuTopRep K n
local notation "D" A:arg => discreteLinearDual (R := ℤ) (G := Γabs) A Mu
local notation "Hcoh" => _root_.continuousCohomology (k := ℤ)

variable (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [DiscreteTopology A]
  (H : OpenSubgroup Gal(SeparableClosure K/K))
variable (hn : ((n : ℕ) : K) ≠ 0)

local instance (U : OpenSubgroup Gal(SeparableClosure K/K)) :
    LocallyCompactSpace U.toSubgroup := U.isClosed.locallyCompactSpace

local notation "R" X => TopRep.res H.toSubgroup.subtype X
local notation "ev" => discreteLinearDualIntEvaluation A Mu
local notation "evCont" => discreteLinearDualIntEvaluation_continuous A Mu
local notation "evEquiv" => discreteLinearDualIntEvaluation_equivariant A Mu

/-- The arithmetic trace on the open-subgroup cohomology, defined using corestriction. -/
def openLocalTateTrace : Hcoh 2 (R Mu) →+ ZMod (n : ℕ) :=
  (localKummerTrace K n hn).toAddMonoidHom.comp (corestrict Mu H 2)

/-- The degree-zero pairing on the original open-subgroup cochains, with trace by corestriction. -/
def openLocalTatePairingZeroAdjoint : Hcoh 0 (R A) →+ (Hcoh 2 (R (D A)) →+ ZMod (n : ℕ)) := by
  let f := openLocalTateTrace K n H hn
  let h (g : ↥(H : Subgroup Γabs)) := evEquiv (g : Γabs)
  exact pairingAdjoint (fun a b =>
    f (cupZeroTwo (A := R A) (B := R (D A)) (C := R Mu) ev evCont h a b))
    (fun a a' b =>
      (congrArg f (cupZeroTwo_add_left (A := R A) (B := R (D A)) (C := R Mu)
        ev evCont h a a' b)).trans (map_add f _ _))
    (fun a b b' =>
      (congrArg f (cupZeroTwo_add_right (A := R A) (B := R (D A)) (C := R Mu)
        ev evCont h a b b')).trans (map_add f _ _))

/-- The degree-one pairing on the original open-subgroup cochains, with trace by corestriction. -/
def openLocalTatePairingOneAdjoint : Hcoh 1 (R A) →+ (Hcoh 1 (R (D A)) →+ ZMod (n : ℕ)) := by
  let f := openLocalTateTrace K n H hn
  let h (g : ↥(H : Subgroup Γabs)) := evEquiv (g : Γabs)
  exact pairingAdjoint (fun a b =>
    f (cupOneOne (A := R A) (B := R (D A)) (C := R Mu) ev evCont h a b))
    (fun a a' b =>
      (congrArg f (cupOneOne_add_left (A := R A) (B := R (D A)) (C := R Mu)
        ev evCont h a a' b)).trans (map_add f _ _))
    (fun a b b' =>
      (congrArg f (cupOneOne_add_right (A := R A) (B := R (D A)) (C := R Mu)
        ev evCont h a b b')).trans (map_add f _ _))

/-- The degree-two pairing on the original open-subgroup cochains, with trace by corestriction. -/
def openLocalTatePairingTwoAdjoint : Hcoh 2 (R A) →+ (Hcoh 0 (R (D A)) →+ ZMod (n : ℕ)) := by
  let f := openLocalTateTrace K n H hn
  let h (g : ↥(H : Subgroup Γabs)) := evEquiv (g : Γabs)
  exact pairingAdjoint (fun a b =>
    f (cupTwoZero (A := R A) (B := R (D A)) (C := R Mu) ev evCont h a b))
    (fun a a' b =>
      (congrArg f (cupTwoZero_add_left (A := R A) (B := R (D A)) (C := R Mu)
        ev evCont h a a' b)).trans (map_add f _ _))
    (fun a b b' =>
      (congrArg f (cupTwoZero_add_right (A := R A) (B := R (D A)) (C := R Mu)
        ev evCont h a b b')).trans (map_add f _ _))

private theorem localTatePairingZeroAdjoint_eval
    (a : Hcoh 0 A) (b : Hcoh 2 (D A)) :
    localTatePairingZeroAdjoint K n A hn a b =
      (localKummerTrace K n hn).toAddMonoidHom (cupZeroTwo ev evCont evEquiv a b) := rfl

private theorem openLocalTatePairingZeroAdjoint_eval
    (a : Hcoh 0 (R A)) (b : Hcoh 2 (TopRep.res H.toSubgroup.subtype (D A))) :
    openLocalTatePairingZeroAdjoint K n A H hn a b =
      openLocalTateTrace K n H hn
        (cupZeroTwo (A := R A) (B := R (D A)) (C := R Mu) ev evCont
          (fun σ : ↥H.toSubgroup => evEquiv (σ : Γabs)) a b) := rfl

private theorem localTatePairingOneAdjoint_eval
    (a : Hcoh 1 A) (b : Hcoh 1 (D A)) :
    localTatePairingOneAdjoint K n A hn a b =
      (localKummerTrace K n hn).toAddMonoidHom (cupOneOne ev evCont evEquiv a b) := rfl

private theorem openLocalTatePairingOneAdjoint_eval
    (a : Hcoh 1 (R A)) (b : Hcoh 1 (TopRep.res H.toSubgroup.subtype (D A))) :
    openLocalTatePairingOneAdjoint K n A H hn a b =
      openLocalTateTrace K n H hn
        (cupOneOne (A := R A) (B := R (D A)) (C := R Mu) ev evCont
          (fun σ : ↥H.toSubgroup => evEquiv (σ : Γabs)) a b) := rfl

private theorem localTatePairingTwoAdjoint_eval
    (a : Hcoh 2 A) (b : Hcoh 0 (D A)) :
    localTatePairingTwoAdjoint K n A hn a b =
      (localKummerTrace K n hn).toAddMonoidHom (cupTwoZero ev evCont evEquiv a b) := rfl

private theorem openLocalTatePairingTwoAdjoint_eval
    (a : Hcoh 2 (R A)) (b : Hcoh 0 (TopRep.res H.toSubgroup.subtype (D A))) :
    openLocalTatePairingTwoAdjoint K n A H hn a b =
      openLocalTateTrace K n H hn
        (cupTwoZero (A := R A) (B := R (D A)) (C := R Mu) ev evCont
          (fun σ : ↥H.toSubgroup => evEquiv (σ : Γabs)) a b) := rfl

/-- The three perfect pairings descend through the actual restriction and
corestriction whenever the open subgroup has index prime to the exponent. -/
theorem localTatePairingAdjoints_bijective_of_primeToIndex_openSubgroup
    [Fact (n : ℕ).Prime] (hindex : ¬ (n : ℕ) ∣ H.toSubgroup.index)
    (hA : ∀ a : A, (n : ℕ) • a = 0)
    (hzero : Function.Bijective (openLocalTatePairingZeroAdjoint K n A H hn))
    (hone : Function.Bijective (openLocalTatePairingOneAdjoint K n A H hn))
    (htwo : Function.Bijective (openLocalTatePairingTwoAdjoint K n A H hn)) :
    Function.Bijective (localTatePairingZeroAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n A hn) := by
  let f := localKummerTrace K n hn
  have hD := separableMu_dual_nsmul_eq_zero K n A
  have hcohA (i : ℕ) := nsmul_continuousCohomology_eq_zero_of_coefficients A n hA i
  have hcohD (i : ℕ) := nsmul_continuousCohomology_eq_zero_of_coefficients (D A) n hD i
  have hcohD' (i : ℕ) := nsmul_continuousCohomology_eq_zero_of_coefficients (R (D A)) n hD i
  constructor
  · exact bijective_addHom_pairing_of_primeToIndex n H.toSubgroup.index hindex
      (localTatePairingZeroAdjoint K n A hn) (openLocalTatePairingZeroAdjoint K n A H hn)
      (openRestriction A H 0) (openRestriction (D A) H 2) (corestrict A H 0) (corestrict (D A) H 2)
      (hcohA 0) (hcohD 2) (hcohD' 2)
      (corestrict_openRestriction_zero A H) (corestrict_openRestriction_two (D A) H)
      (fun a b => congrArg f (corestrict_cupZeroTwo_left H ev evCont evEquiv a b))
      (fun a b => congrArg f (corestrict_cupZeroTwo_right H ev evCont evEquiv a b)) hzero
  · constructor
    · exact bijective_addHom_pairing_of_primeToIndex n H.toSubgroup.index hindex
        (localTatePairingOneAdjoint K n A hn) (openLocalTatePairingOneAdjoint K n A H hn)
        (openRestriction A H 1) (openRestriction (D A) H 1)
        (corestrict A H 1) (corestrict (D A) H 1)
        (hcohA 1) (hcohD 1) (hcohD' 1)
        (corestrict_openRestriction_one H A) (corestrict_openRestriction_one H (D A))
        (fun a b => congrArg f (corestrict_cupOneOne_left H ev evCont evEquiv a b))
        (fun a b => congrArg f (corestrict_cupOneOne_right H ev evCont evEquiv a b)) hone
    · exact bijective_addHom_pairing_of_primeToIndex n H.toSubgroup.index hindex
        (localTatePairingTwoAdjoint K n A hn) (openLocalTatePairingTwoAdjoint K n A H hn)
        (openRestriction A H 2) (openRestriction (D A) H 0)
        (corestrict A H 2) (corestrict (D A) H 0)
        (hcohA 2) (hcohD 0) (hcohD' 0)
        (corestrict_openRestriction_two A H) (corestrict_openRestriction_zero (D A) H)
        (fun a b => congrArg f (corestrict_cupTwoZero_left H ev evCont evEquiv a b))
        (fun a b => congrArg f (corestrict_cupTwoZero_right H ev evCont evEquiv a b)) htwo

/-- Transport a discrete linear dual along the same subgroup action and coefficient map. -/
def dualAfterRestriction {G J H : Type u} [Group G] [Group J] [Group H]
    [TopologicalSpace J] [TopologicalSpace H] (e : H ≃ₜ* J) (s : J →* G)
    (A N : TopRep.{u} ℤ G) (M : TopRep.{u} ℤ H)
    (μ : TopRep.res e.symm.toMonoidHom M ⟶ TopRep.res s N) :
    TopRep.res e.symm.toMonoidHom
        (discreteLinearDual (TopRep.res e.toMonoidHom (TopRep.res s A)) M) ⟶
      TopRep.res s (discreteLinearDual A N) := by
  let V := TopRep.res e.toMonoidHom (TopRep.res s A)
  let W := discreteLinearDual V M
  let Z := discreteLinearDual A N
  let X := TopRep.res e.symm.toMonoidHom W
  let Y := TopRep.res s Z
  let : Module ℤ X := X.hV2
  let : Module ℤ Y := Y.hV2
  let : Module ℤ A := A.hV2
  let : Module ℤ M := M.hV2
  let : Module ℤ N := N.hV2
  let μ₀ : M →ₗ[ℤ] N := μ.hom.toContinuousLinearMap.toLinearMap
  let f := LinearMap.llcomp (σ₁₂ := RingHom.id ℤ) (σ₂₃ := RingHom.id ℤ)
    (σ₁₃ := RingHom.id ℤ) ℤ A M N μ₀
  exact ConcreteCategory.ofHom (C := TopRep.{u} ℤ J) (X := X) (Y := Y)
    { toLinearMap := f
      cont := continuous_of_discreteTopology
      isIntertwining' := fun σ => by
        apply ContinuousLinearMap.ext
        intro l
        change discreteLinearDualMap A N (f (W.ρ (e.symm σ) l)) =
          discreteLinearDualMap A N (Z.ρ (s σ) (f l))
        apply LinearMap.ext
        intro a
        have hs : e ((e.symm σ)⁻¹) = σ⁻¹ := by rw [map_inv, e.apply_symm_apply]
        let l₀ := discreteLinearDualMap V M l
        change μ (M.ρ (e.symm σ) (l₀ (A.ρ (s (e ((e.symm σ)⁻¹))) a))) =
          N.ρ (s σ) (μ (l₀ (A.ρ ((s σ)⁻¹) a)))
        rw [hs, map_inv]
        exact TopRep.hom_comm_apply μ σ _ }

private theorem bijective_pairing_of_transport {X Y X' Y' : Type u} {T : Type*}
    [AddZeroClass X] [AddZeroClass Y] [AddZeroClass X'] [AddZeroClass Y'] [AddCommMonoid T]
    (P : X →+ (Y →+ T)) (P' : X' →+ (Y' →+ T))
    (s : X →+ X') (t : Y →+ Y') (hs : Function.Bijective s) (ht : Function.Bijective t)
    (h : ∀ a b, P' (s a) (t b) = P a b) (hP : Function.Bijective P) : Function.Bijective P' := by
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := hs.surjective a
    obtain ⟨b, rfl⟩ := hs.surjective b
    apply congrArg s
    apply hP.injective
    exact AddMonoidHom.ext fun x =>
      (h a x).symm.trans ((DFunLike.congr_fun hab (t x)).trans (h b x))
  · intro l
    obtain ⟨a, ha⟩ := hP.surjective (l.comp t)
    refine ⟨s a, AddMonoidHom.ext fun y => ?_⟩
    obtain ⟨b, rfl⟩ := ht.surjective y
    exact (h a b).trans (DFunLike.congr_fun ha b)

section Embedded

@[reducible] noncomputable local instance canonicalSeparableClosureAlgebra
    (F : Type u) [Field F] : Algebra F (SeparableClosure F) :=
  IntermediateField.algebra' (separableClosure F (AlgebraicClosure F))

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
variable (j : SeparableClosure K ≃ₐ[E] SeparableClosure E)

local notation "S" => stageOpenFixingSubgroup K E
local notation "I" => OpenSubgroup.toSubgroup S
local notation "e" => embeddedAbsoluteRestrictionEquiv K E j
local notation "RS" X => TopRep.res (Subgroup.subtype I) X

/-- The original coefficients over the embedded field carry the restricted action. -/
abbrev embeddedTateCoefficients : TopRep.{u} ℤ Gal(SeparableClosure E/E) :=
  TopRep.res (e).toMonoidHom (RS A)

local notation "V" => embeddedTateCoefficients K A E j
local notation "MuE" => separableMuTopRep E n
local notation "DE" =>
  discreteLinearDual (G := Gal(SeparableClosure E/E)) (V) (MuE)

local instance embeddedTateCoefficients_discrete : DiscreteTopology V :=
  inferInstanceAs (DiscreteTopology A)

/-- The dual transport is actual postcomposition with the bijective Kummer
coefficient map on the same original linear maps. -/
def embeddedTateDualTransport :=
  dualAfterRestriction (embeddedAbsoluteRestrictionEquiv K E j)
    (stageOpenFixingSubgroup K E).toSubgroup.subtype A (separableMuTopRep K n)
    (separableMuTopRep E n) (embeddedMuTransport K E j n)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [DiscreteTopology ↑A] in
theorem embeddedTateDualTransport_bijective :
    Function.Bijective (embeddedTateDualTransport K n A E j) := by
  let M := separableMuTopRep E n
  let N := separableMuTopRep K n
  let μ := embeddedMuTransport K E j n
  let : Module ℤ A := A.hV2
  let : Module ℤ M := M.hV2
  let : Module ℤ N := N.hV2
  let μ₀ : M →ₗ[ℤ] N := μ.hom.toContinuousLinearMap.toLinearMap
  let ζ := LinearEquiv.ofBijective μ₀ (embeddedMuTransport_bijective K E j n)
  constructor
  · intro a b hab
    change discreteLinearDualMap V M a = discreteLinearDualMap V M b
    apply LinearMap.ext
    intro x
    apply ζ.injective
    exact congrArg (fun l : D A => discreteLinearDualMap A N l x) hab
  · intro l
    let l₀ : DE := ζ.symm.toLinearMap.comp (discreteLinearDualMap A N l)
    refine ⟨l₀, ?_⟩
    change discreteLinearDualMap A N (embeddedTateDualTransport K n A E j l₀) =
      discreteLinearDualMap A N l
    exact LinearMap.ext fun x => ζ.apply_symm_apply (discreteLinearDualMap A N l x)

attribute [local instance] embeddedStageSpectralNormedField embeddedStageSpectralValuativeRel
  embeddedStageSpectralLocalField

private def embeddedTateCoefficientIso :=
  discreteCoefficientIsoOfBijective (restrictionInverseHom (e) (RS A))
    (Function.bijective_id : Function.Bijective (id : A → A))

private def embeddedTateDualIso :=
  discreteCoefficientIsoOfBijective (embeddedTateDualTransport K n A E j)
    (embeddedTateDualTransport_bijective K n A E j)

private theorem embeddedTateTrace_map (hnE : ((n : ℕ) : E) ≠ 0)
    (x : Hcoh 2 MuE) :
    openLocalTateTrace K n S hn (embeddedMuCohomologyTransport K E j n x) =
      localKummerTrace E n hnE x :=
  localKummerTrace_embeddedCorestriction K E j n hn hnE x

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedTatePairing_evaluation (a : V) (b : DE) :
    embeddedMuTransport K E j n (discreteLinearDualIntEvaluation V MuE a b) =
      ev ((embeddedTateCoefficientIso K A E j).hom a)
        ((embeddedTateDualIso K n A E j).hom b) := rfl

private def embeddedTateCoefficientCohomologyMap (i : ℕ) :
    Hcoh i V →+ Hcoh i (RS A) :=
  (map (X := V) (Y := RS A) (embeddedAbsoluteRestrictionInverseHom K E j)
    (embeddedTateCoefficientIso K A E j).hom i).hom.toLinearMap.toAddMonoidHom

private def embeddedTateDualCohomologyMap (i : ℕ) :
    Hcoh i DE →+ Hcoh i (RS (D A)) :=
  (map (X := DE) (Y := RS (D A)) (embeddedAbsoluteRestrictionInverseHom K E j)
    (embeddedTateDualIso K n A E j).hom i).hom.toLinearMap.toAddMonoidHom

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedTateCoefficientCohomologyMap_bijective (i : ℕ) :
    Function.Bijective (embeddedTateCoefficientCohomologyMap K A E j i) :=
  map_bijective_of_groupEquiv (e).symm (embeddedTateCoefficientIso K A E j) i

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [DiscreteTopology ↑A] in
private theorem embeddedTateDualCohomologyMap_bijective (i : ℕ) :
    Function.Bijective (embeddedTateDualCohomologyMap K n A E j i) :=
  map_bijective_of_groupEquiv (e).symm (embeddedTateDualIso K n A E j) i

local notation "upperPairing" => discreteLinearDualIntEvaluation V MuE
local notation "upperPairingContinuous" => discreteLinearDualIntEvaluation_continuous V MuE
local notation "upperPairingEquivariant" => discreteLinearDualIntEvaluation_equivariant V MuE

private def embeddedTateZeroCupValue (a : Hcoh 0 V) (b : Hcoh 2 DE) : Hcoh 2 MuE := by
  let G := Gal(SeparableClosure E/E)
  let : Group G := AlgEquiv.aut
  let : TopologicalSpace G := krullTopology E (SeparableClosure E)
  let : IsTopologicalGroup G := inferInstance
  let : LocallyCompactSpace G := separableAbsoluteGalois_locallyCompact E
  let pairing := upperPairing
  let continuousPairing := upperPairingContinuous
  let equivariantPairing := upperPairingEquivariant
  let value := cupZeroTwo (G := G) (A := V) (B := DE) (C := MuE)
    pairing continuousPairing equivariantPairing a b
  with_reducible exact value

private def fixingSubgroupTateZeroCupValue
    (a : Hcoh 0 (RS A)) (b : Hcoh 2 (RS(D A))) : Hcoh 2 (RS Mu) :=
  cupZeroTwo (A := RS A) (B := RS (D A)) (C := RS Mu) ev evCont
    (fun σ : I => evEquiv (σ : Γabs)) a b

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedTateZeroCup_map (a : Hcoh 0 V) (b : Hcoh 2 DE) :
    let f : Hcoh 2 MuE →+ Hcoh 2 (RS Mu) := embeddedMuCohomologyTransport K E j n
    let x := embeddedTateZeroCupValue K n A E j a b
    let y := fixingSubgroupTateZeroCupValue K n A E
      (embeddedTateCoefficientCohomologyMap K A E j 0 a)
      (embeddedTateDualCohomologyMap K n A E j 2 b)
    f x = y := by
  intro valueMap cup cup'
  let G := Gal(SeparableClosure E/E)
  let galGroup : Group G := AlgEquiv.aut
  let galTopology : TopologicalSpace G := krullTopology E (SeparableClosure E)
  let galTopGroup : IsTopologicalGroup G := inferInstance
  let galCompact : LocallyCompactSpace G := separableAbsoluteGalois_locallyCompact E
  let r := embeddedAbsoluteRestrictionInverseHom K E j
  let f := (embeddedTateCoefficientIso K A E j).hom
  let g := (embeddedTateDualIso K n A E j).hom
  let k := embeddedMuTransport K E j n
  let q' (σ : I) := evEquiv (σ : Γabs)
  have h := embeddedTatePairing_evaluation K n A E j
  have hmap := map_cupZeroTwo (G := G) (A := V) (B := DE) (C := MuE)
    (A' := RS A) (B' := RS (D A)) (C' := RS Mu)
    upperPairing upperPairingContinuous upperPairingEquivariant r f g k ev evCont q' h a b
  refine Eq.trans ?_ (Eq.trans hmap ?_)
  · rfl
  · rfl

private theorem embeddedTateZeroAdjoint_bijective
    (hnE : ((n : ℕ) : E) ≠ 0) :
    let lower := openLocalTatePairingZeroAdjoint K n A S hn
    let upper := localTatePairingZeroAdjoint E n V hnE
    Function.Bijective upper → Function.Bijective lower := by
  intro lower upper hb
  let f := embeddedTateCoefficientCohomologyMap K A E j 0
  let g := embeddedTateDualCohomologyMap K n A E j 2
  have hf := embeddedTateCoefficientCohomologyMap_bijective K A E j 0
  have hg := embeddedTateDualCohomologyMap_bijective K n A E j 2
  let transport := bijective_pairing_of_transport upper lower
  let transportFirst := transport f
  let transportSecond := transportFirst g
  refine transportSecond hf hg ?_ hb
  intro a b
  let y := embeddedTateZeroCupValue K n A E j a b
  let trace := openLocalTateTrace K n S hn
  have hleft := openLocalTatePairingZeroAdjoint_eval K n A S hn (f a) (g b)
  have hcup := congrArg trace (embeddedTateZeroCup_map K n A E j a b).symm
  have htrace := embeddedTateTrace_map K n hn E j hnE y
  have hright := localTatePairingZeroAdjoint_eval E n V hnE a b
  refine hleft.trans ?_
  refine hcup.trans ?_
  refine htrace.trans ?_
  exact hright.symm

private def embeddedTateOneCupValue (a : Hcoh 1 V) (b : Hcoh 1 DE) : Hcoh 2 MuE := by
  let G := Gal(SeparableClosure E/E)
  let : Group G := AlgEquiv.aut
  let : TopologicalSpace G := krullTopology E (SeparableClosure E)
  let : IsTopologicalGroup G := inferInstance
  let : LocallyCompactSpace G := separableAbsoluteGalois_locallyCompact E
  let pairing := upperPairing
  let continuousPairing := upperPairingContinuous
  let equivariantPairing := upperPairingEquivariant
  let value := cupOneOne (G := G) (A := V) (B := DE) (C := MuE)
    pairing continuousPairing equivariantPairing a b
  with_reducible exact value

private def fixingSubgroupTateOneCupValue
    (a : Hcoh 1 (RS A)) (b : Hcoh 1 (RS(D A))) : Hcoh 2 (RS Mu) :=
  cupOneOne (A := RS A) (B := RS (D A)) (C := RS Mu) ev evCont
    (fun σ : I => evEquiv (σ : Γabs)) a b

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedTateOneCup_map (a : Hcoh 1 V) (b : Hcoh 1 DE) :
    let f : Hcoh 2 MuE →+ Hcoh 2 (RS Mu) := embeddedMuCohomologyTransport K E j n
    let x := embeddedTateOneCupValue K n A E j a b
    let y := fixingSubgroupTateOneCupValue K n A E
      (embeddedTateCoefficientCohomologyMap K A E j 1 a)
      (embeddedTateDualCohomologyMap K n A E j 1 b)
    f x = y := by
  intro valueMap cup cup'
  let G := Gal(SeparableClosure E/E)
  let galGroup : Group G := AlgEquiv.aut
  let galTopology : TopologicalSpace G := krullTopology E (SeparableClosure E)
  let galTopGroup : IsTopologicalGroup G := inferInstance
  let galCompact : LocallyCompactSpace G := separableAbsoluteGalois_locallyCompact E
  let r := embeddedAbsoluteRestrictionInverseHom K E j
  let f := (embeddedTateCoefficientIso K A E j).hom
  let g := (embeddedTateDualIso K n A E j).hom
  let k := embeddedMuTransport K E j n
  let q' (σ : I) := evEquiv (σ : Γabs)
  have h := embeddedTatePairing_evaluation K n A E j
  have hmap := map_cupOneOne (G := G) (A := V) (B := DE) (C := MuE)
    (A' := RS A) (B' := RS (D A)) (C' := RS Mu)
    upperPairing upperPairingContinuous upperPairingEquivariant r f g k ev evCont q' h a b
  refine Eq.trans ?_ (Eq.trans hmap ?_)
  · rfl
  · rfl

private theorem embeddedTateOneAdjoint_bijective
    (hnE : ((n : ℕ) : E) ≠ 0) :
    let lower := openLocalTatePairingOneAdjoint K n A S hn
    let upper := localTatePairingOneAdjoint E n V hnE
    Function.Bijective upper → Function.Bijective lower := by
  intro lower upper hb
  let f := embeddedTateCoefficientCohomologyMap K A E j 1
  let g := embeddedTateDualCohomologyMap K n A E j 1
  have hf := embeddedTateCoefficientCohomologyMap_bijective K A E j 1
  have hg := embeddedTateDualCohomologyMap_bijective K n A E j 1
  let transport := bijective_pairing_of_transport upper lower
  let transportFirst := transport f
  let transportSecond := transportFirst g
  refine transportSecond hf hg ?_ hb
  intro a b
  let y := embeddedTateOneCupValue K n A E j a b
  let trace := openLocalTateTrace K n S hn
  have hleft := openLocalTatePairingOneAdjoint_eval K n A S hn (f a) (g b)
  have hcup := congrArg trace (embeddedTateOneCup_map K n A E j a b).symm
  have htrace := embeddedTateTrace_map K n hn E j hnE y
  have hright := localTatePairingOneAdjoint_eval E n V hnE a b
  refine hleft.trans ?_
  refine hcup.trans ?_
  refine htrace.trans ?_
  exact hright.symm

private def embeddedTateTwoCupValue (a : Hcoh 2 V) (b : Hcoh 0 DE) : Hcoh 2 MuE := by
  let G := Gal(SeparableClosure E/E)
  let : Group G := AlgEquiv.aut
  let : TopologicalSpace G := krullTopology E (SeparableClosure E)
  let : IsTopologicalGroup G := inferInstance
  let : LocallyCompactSpace G := separableAbsoluteGalois_locallyCompact E
  let pairing := upperPairing
  let continuousPairing := upperPairingContinuous
  let equivariantPairing := upperPairingEquivariant
  let value := cupTwoZero (G := G) (A := V) (B := DE) (C := MuE)
    pairing continuousPairing equivariantPairing a b
  with_reducible exact value

private def fixingSubgroupTateTwoCupValue
    (a : Hcoh 2 (RS A)) (b : Hcoh 0 (RS(D A))) : Hcoh 2 (RS Mu) :=
  cupTwoZero (A := RS A) (B := RS (D A)) (C := RS Mu) ev evCont
    (fun σ : I => evEquiv (σ : Γabs)) a b

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedTateTwoCup_map (a : Hcoh 2 V) (b : Hcoh 0 DE) :
    let f : Hcoh 2 MuE →+ Hcoh 2 (RS Mu) := embeddedMuCohomologyTransport K E j n
    let x := embeddedTateTwoCupValue K n A E j a b
    let y := fixingSubgroupTateTwoCupValue K n A E
      (embeddedTateCoefficientCohomologyMap K A E j 2 a)
      (embeddedTateDualCohomologyMap K n A E j 0 b)
    f x = y := by
  intro valueMap cup cup'
  let G := Gal(SeparableClosure E/E)
  let galGroup : Group G := AlgEquiv.aut
  let galTopology : TopologicalSpace G := krullTopology E (SeparableClosure E)
  let galTopGroup : IsTopologicalGroup G := inferInstance
  let galCompact : LocallyCompactSpace G := separableAbsoluteGalois_locallyCompact E
  let r := embeddedAbsoluteRestrictionInverseHom K E j
  let f := (embeddedTateCoefficientIso K A E j).hom
  let g := (embeddedTateDualIso K n A E j).hom
  let k := embeddedMuTransport K E j n
  let q' (σ : I) := evEquiv (σ : Γabs)
  have h := embeddedTatePairing_evaluation K n A E j
  have hmap := map_cupTwoZero (G := G) (A := V) (B := DE) (C := MuE)
    (A' := RS A) (B' := RS (D A)) (C' := RS Mu)
    upperPairing upperPairingContinuous upperPairingEquivariant r f g k ev evCont q' h a b
  refine Eq.trans ?_ (Eq.trans hmap ?_)
  · rfl
  · rfl

private theorem embeddedTateTwoAdjoint_bijective
    (hnE : ((n : ℕ) : E) ≠ 0) :
    let lower := openLocalTatePairingTwoAdjoint K n A S hn
    let upper := localTatePairingTwoAdjoint E n V hnE
    Function.Bijective upper → Function.Bijective lower := by
  intro lower upper hb
  let f := embeddedTateCoefficientCohomologyMap K A E j 2
  let g := embeddedTateDualCohomologyMap K n A E j 0
  have hf := embeddedTateCoefficientCohomologyMap_bijective K A E j 2
  have hg := embeddedTateDualCohomologyMap_bijective K n A E j 0
  let transport := bijective_pairing_of_transport upper lower
  let transportFirst := transport f
  let transportSecond := transportFirst g
  refine transportSecond hf hg ?_ hb
  intro a b
  let y := embeddedTateTwoCupValue K n A E j a b
  let trace := openLocalTateTrace K n S hn
  have hleft := openLocalTatePairingTwoAdjoint_eval K n A S hn (f a) (g b)
  have hcup := congrArg trace (embeddedTateTwoCup_map K n A E j a b).symm
  have htrace := embeddedTateTrace_map K n hn E j hnE y
  have hright := localTatePairingTwoAdjoint_eval E n V hnE a b
  refine hleft.trans ?_
  refine hcup.trans ?_
  refine htrace.trans ?_
  exact hright.symm

/-- The perfect pairings for the embedded finite extension transport to the
actual open fixing subgroup, with the same local arithmetic trace. -/
theorem openLocalTatePairingAdjoints_bijective_of_embedded
    (hnE : ((n : ℕ) : E) ≠ 0)
    (hzero : Function.Bijective (localTatePairingZeroAdjoint E n V hnE))
    (hone : Function.Bijective (localTatePairingOneAdjoint E n V hnE))
    (htwo : Function.Bijective (localTatePairingTwoAdjoint E n V hnE)) :
    Function.Bijective (openLocalTatePairingZeroAdjoint K n A S hn) ∧
      Function.Bijective (openLocalTatePairingOneAdjoint K n A S hn) ∧
      Function.Bijective (openLocalTatePairingTwoAdjoint K n A S hn) := by
  exact ⟨embeddedTateZeroAdjoint_bijective K n A hn E j hnE hzero,
    embeddedTateOneAdjoint_bijective K n A hn E j hnE hone,
    embeddedTateTwoAdjoint_bijective K n A hn E j hnE htwo⟩

end Embedded

end ClassFieldTheory.Brauer
