/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClassTower
public import Nyll.GaloisCohomology.Cyclic.IntegralHilbert90
public import Nyll.GaloisCohomology.Cyclic.IntegralTateNakayama
public import Nyll.GaloisCohomology.Cyclic.IntegralTateRestrictionComparison
public import Nyll.GaloisCohomology.GroupTheory.H2EquivariantEquivalence

/-!
# The local Tate–Nakayama isomorphism on the original field units

The embedded local invariant supplies the original degree-two fundamental
class. Its subgroup restrictions are compared with the relative restrictions
to the fixed fields. Hilbert 90 and the orders of these restricted classes
then give the Tate–Nakayama isomorphism with the original cup map.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Module
open ContinuousCohomology ClassFieldTower.Cohomology LocalFieldTheory
open IntegralGroupCohomology.Universe
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

private theorem liftedUnits_action_restrictScalars
    {K F M : Type u} [Field K] [Field F] [Field M]
    [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
    (σ : Gal(M/K)) (τ : Gal(M/F)) (h : σ = AlgEquiv.restrictScalarsHom K τ)
    (a : Additive Mˣ) :
    ((liftedGaloisUnitsRep K M).ρ σ a : Additive Mˣ) =
      ((liftedGaloisUnitsRep F M).ρ τ a : Additive Mˣ) := by
  subst σ
  rfl

/-- Positive Tate comparison and the actual unit restriction give the same
pullback after transporting the group and the units. -/
private theorem tateH2_equiv_restrict
    {G : Type v} [Group G] [Fintype G] (U : Rep.{v} ℤ G)
    (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]
    (K F M : Type u) [Field K] [Field F] [Field M]
    [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
    [FiniteDimensional K M] [FiniteDimensional F M]
    (e : G ≃* Gal(M/K)) (eH : H ≃* Gal(M/F))
    (k : (IntegralGroupCohomology.coefficientFunctor G).obj U ≃+ liftedGaloisUnitsRep K M)
    (kH : (IntegralGroupCohomology.coefficientFunctor H).obj (Rep.res H.subtype U)
      ≃+ liftedGaloisUnitsRep F M)
    (hk : ∀ g a, k (((IntegralGroupCohomology.coefficientFunctor G).obj U).ρ g a) =
      (liftedGaloisUnitsRep K M).ρ (e g) (k a))
    (hkH : ∀ g a, kH (((IntegralGroupCohomology.coefficientFunctor H).obj
      (Rep.res H.subtype U)).ρ g a) = (liftedGaloisUnitsRep F M).ρ (eH g) (kH a))
    (he : ∀ g : H, e g.val = AlgEquiv.restrictScalarsHom K (eH g))
    (hunits : ∀ a : (IntegralGroupCohomology.coefficientFunctor G).obj U, kH a = k a)
    (x : tate U 2) :
    let cK := continuousRelativeUnitsH2Equiv K M
    let cF := continuousRelativeUnitsH2Equiv F M
    let pK := groupCohomology.equivariantH2AddEquiv e k hk
    let pF := groupCohomology.equivariantH2AddEquiv eH kH hkH
    cF.symm (pF ((tatePositiveIsoCommonCohomology (Rep.res H.subtype U) 2).hom
      (tateRestrict H U 2 x))) = relativeBaseRestriction K F M
        (cK.symm (pK ((tatePositiveIsoCommonCohomology U 2).hom x))) := by
  intro cK cF pK pF
  let R := (IntegralGroupCohomology.coefficientFunctor G).obj U
  let R' := (IntegralGroupCohomology.coefficientFunctor H).obj (Rep.res H.subtype U)
  let z : groupCohomology.H2 R := (tatePositiveIsoCommonCohomology U 2).hom x
  let q : Gal(M/F) →* Gal(M/K) := AlgEquiv.restrictScalarsHom K
  let f := liftedFiniteGaloisTowerUnitsRestrictionRepHom K F M
  have hcoeff (a : R) : kH ((𝟙 R') a) = f (k a) := hunits a
  have hr : (tatePositiveIsoCommonCohomology (Rep.res H.subtype U) 2).hom
      (tateRestrict H U 2 x) = groupCohomology.map H.subtype (𝟙 R') 2 z :=
    tateRestrict_positive_comp_common H 2 U x
  have hm : pF (groupCohomology.map H.subtype (𝟙 R') 2 z) =
      liftedFiniteGaloisTowerUnitsH2Restriction K F M (pK z) :=
    groupCohomology.equivariantH2AddEquiv_map e k hk eH kH hkH H.subtype q (𝟙 R') f he hcoeff z
  apply cF.injective
  rw [cF.apply_symm_apply, continuousRelativeUnitsH2Equiv_baseRestriction, cK.apply_symm_apply]
  exact (congrArg (pF : groupCohomology.H2 R' → _) hr).trans hm

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

local instance {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "U" => Rep.ofAlgebraAutOnUnits K L
/-- The finite Galois group in the representation universe used by Tate cup. -/
abbrev localLiftedGaloisGroup := ULift.{v} Gal(L/K)

local notation "J" => localLiftedGaloisGroup K L

/-- The original unit representation after the single auxiliary lift used by Tate cup. -/
abbrev localLiftedUnitsRepresentation : Rep.{v} ℤ J := (Rep.universeLiftFunctor ℤ Gal(L/K)).obj U

variable (i : L →ₐ[K] SeparableClosure K)

local notation "E" => fundamentalClassStage K L i
local notation "V" => localLiftedUnitsRepresentation K L

/-- The group equivalence induced by the chosen embedding of the original extension. -/
def localLiftedStageGroupEquiv : J ≃* Gal(E/K) :=
  (MulEquiv.ulift : J ≃* Gal(L/K)).trans (AlgEquiv.autCongr i.equivFieldRange)

/-- The actual unit map to the embedded field, after removing the auxiliary carrier lift. -/
def localLiftedStageUnitsEquiv : V ≃+ liftedGaloisUnitsRep K E :=
  ((ULift.moduleEquiv : ULift.{v} (Additive Lˣ) ≃ₗ[ℤ] Additive Lˣ).toAddEquiv).trans
    (Units.mapEquiv i.equivFieldRange.toMulEquiv).toAdditive

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem localLiftedStageUnitsEquiv_comm (g : J) (a : V) :
    localLiftedStageUnitsEquiv K L i ((V).ρ g a) =
      (liftedGaloisUnitsRep K E).ρ (localLiftedStageGroupEquiv K L i g)
        (localLiftedStageUnitsEquiv K L i a) :=
  unitsMapEquiv_action K L E i.equivFieldRange g.down a.down

/-- The positive Tate comparison leads to the very same finite relative
degree-two classes on the embedded extension. -/
def localLiftedTateH2EmbeddedEquiv : tate V 2 ≃+ relativeBr E :=
  ((tatePositiveIsoCommonCohomology V 2).toLinearEquiv.toAddEquiv).trans
    ((groupCohomology.equivariantH2AddEquiv
      (A := (IntegralGroupCohomology.coefficientFunctor J).obj V) (B := liftedGaloisUnitsRep K E)
      (localLiftedStageGroupEquiv K L i)
      (localLiftedStageUnitsEquiv K L i) (localLiftedStageUnitsEquiv_comm K L i)).trans
      (continuousRelativeUnitsH2Equiv K E).symm)

/-- The fundamental class on the original unit Tate group is the original
relative H² class carried through the same field, cochain, and Tate comparisons. -/
def localFundamentalTateClass : tate U 2 :=
  (tateIsoCommon V 2).hom ((localLiftedTateH2EmbeddedEquiv K L i).symm
    (fundamentalClassStageEquiv K L i (localFundamentalClassOfEmbedding K L i)))

theorem localFundamentalTateClass_lift (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] (i : L →ₐ[K] SeparableClosure K) :
    localLiftedTateH2EmbeddedEquiv K L i
        ((tateIsoCommon (localLiftedUnitsRepresentation K L) 2).inv
          (localFundamentalTateClass K L i)) =
      localFundamentalClass K (fundamentalClassStage K L i) := by
  unfold localFundamentalTateClass localFundamentalClassOfEmbedding
  rw [Iso.hom_inv_id_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsGalois K L] in
/-- Hilbert 90 holds on every actual subgroup of the lifting group. -/
theorem localLiftedTateH1_isZero (H : Subgroup J) : IsZero (tate (Rep.res H.subtype V) 1) := by
  let ρ := (MulEquiv.ulift : J ≃* Gal(L/K)).toMonoidHom.comp H.subtype
  let B := Rep.res ρ U
  let e : Rep.res H.subtype V ≅ B := Rep.mkIso (Representation.Equiv.mk
    (ULift.moduleEquiv : ULift.{v} (Additive Lˣ) ≃ₗ[ℤ] Additive Lˣ) (fun _ => rfl))
  have hρ : Function.Injective ρ :=
    (MulEquiv.ulift : J ≃* Gal(L/K)).injective.comp Subtype.val_injective
  exact ((unitsH1_isZero_of_injective K L ρ hρ).of_iso (tatePositiveIsoCohomology B 1)).of_iso
    ((tateFunctor H 1).mapIso e)

/-- A generator in the target of an additive equivalence generates its source. -/
private theorem exists_zsmul_eq_of_addEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (y : A) (z : B)
    (hy : e y = z) (hgen : ∀ b : B, ∃ m : ℤ, m • z = b) (x : A) :
    ∃ m : ℤ, m • y = x := by
  obtain ⟨m, hm⟩ := hgen (e x)
  exact ⟨m, e.injective ((map_zsmul e m y).trans ((congrArg (m • ·) hy).trans hm))⟩

/-- The relative degree-two group on each actual subgroup has the subgroup's
order and is generated by the literal restriction of the fundamental class. -/
theorem localLiftedTateH2_restriction_properties (H : Subgroup J) [Fintype (J ⧸ H)] :
    Nat.card (tate (Rep.res H.subtype V) 2) = Nat.card H ∧
      ∀ z : tate (Rep.res H.subtype V) 2, ∃ m : ℤ,
        m • tateRestrict H V 2 ((tateIsoCommon V 2).inv (localFundamentalTateClass K L i)) = z := by
  let e := localLiftedStageGroupEquiv K L i
  let T := H.map e.toMonoidHom
  let F₀ := IntermediateField.fixedField T
  let F : IntermediateField K (SeparableClosure K) := IntermediateField.lift F₀
  have h : F ≤ (E).toIntermediateField := IntermediateField.lift_le F₀
  let : Algebra F E := nestedStageAlgebra F E h
  let : IsScalarTower K F E := nestedStageTower F E h
  let : FiniteDimensional K F := (IntermediateField.liftAlgEquiv F₀).toLinearEquiv.finiteDimensional
  let : FiniteDimensional F E := nestedStageFinite F E h
  let : IsGalois F E := IsGalois.tower_top_of_isGalois K F E
  let e₀ := IntermediateField.liftAlgEquiv F₀
  let eT : T ≃* Gal(E/F) :=
    ((MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField T).symm).trans
      (IntermediateField.fixingSubgroupEquiv F₀)).trans
      (ClassFieldTheory.semilinearGaloisEquiv e₀.toRingEquiv (RingEquiv.refl E) (fun _ => rfl))
  let eH := (H.equivMapOfInjective e.toMonoidHom e.injective).trans eT
  have he (g : H) : e (g : J) = AlgEquiv.restrictScalarsHom K (eH g) := by
    apply AlgEquiv.ext
    intro a
    rfl
  let k := localLiftedStageUnitsEquiv K L i
  let R' := (IntegralGroupCohomology.coefficientFunctor H).obj (Rep.res H.subtype V)
  let kH : R' ≃+ liftedGaloisUnitsRep F E := k
  have hkH (g : H) (a : R') : kH (R'.ρ g a) = (liftedGaloisUnitsRep F E).ρ (eH g) (kH a) := by
    let aV : V := a
    let b : Additive (E : Type u)ˣ := k aV
    have hAction : ((liftedGaloisUnitsRep K E).ρ (e g.val) b : Additive (E : Type u)ˣ) =
        ((liftedGaloisUnitsRep F E).ρ (eH g) b : Additive (E : Type u)ˣ) :=
      liftedUnits_action_restrictScalars (K := K) (F := F) (M := E) (e g.val) (eH g) (he g) b
    exact (localLiftedStageUnitsEquiv_comm K L i g.val aV).trans hAction
  let cF := continuousRelativeUnitsH2Equiv F E
  let pF := groupCohomology.equivariantH2AddEquiv (A := R') (B := liftedGaloisUnitsRep F E)
    eH kH hkH
  let eF : tate (Rep.res H.subtype V) 2 ≃+ continuousCohomology 2 (galoisUnitsRep F E) :=
    ((tatePositiveIsoCommonCohomology (Rep.res H.subtype V) 2).toLinearEquiv.toAddEquiv).trans
      (pF.trans cF.symm)
  have hcomp (x : tate V 2) : eF (tateRestrict H V 2 x) =
      relativeBaseRestriction K F E (localLiftedTateH2EmbeddedEquiv K L i x) :=
    tateH2_equiv_restrict V H K F E e eH k kH
      (localLiftedStageUnitsEquiv_comm K L i) hkH he (fun _ => rfl) x
  let y := tateRestrict H V 2 ((tateIsoCommon V 2).inv (localFundamentalTateClass K L i))
  let z := relativeBaseRestriction K F E (localFundamentalClass K E)
  have hy : eF y = z :=
    (hcomp ((tateIsoCommon V 2).inv (localFundamentalTateClass K L i))).trans
      (congrArg (relativeBaseRestriction K F E) (localFundamentalTateClass_lift K L i))
  have hgen := localFundamentalClass_restriction_generates K E F h
  have horder : addOrderOf z = Nat.card H := by
    change addOrderOf (relativeBaseRestriction K F E (localFundamentalClass K E)) = _
    rw [localFundamentalClass_restriction_addOrder K E F h, ← IsGalois.card_aut_eq_finrank F E]
    exact (Nat.card_congr eH.toEquiv).symm
  constructor
  · let S := AddSubgroup.zmultiples z
    have hS : Function.Surjective S.subtype := by
      intro a
      obtain ⟨m, hm⟩ := hgen a
      exact ⟨⟨a, ⟨m, hm⟩⟩, rfl⟩
    calc
      Nat.card (tate (Rep.res H.subtype V) 2) =
          Nat.card (continuousCohomology 2 (galoisUnitsRep F E)) :=
        Nat.card_congr eF.toEquiv
      _ = Nat.card S :=
        (Nat.card_congr (Equiv.ofBijective S.subtype ⟨S.subtype_injective, hS⟩)).symm
      _ = Nat.card H := (Nat.card_zmultiples z).trans horder
  · exact exists_zsmul_eq_of_addEquiv eF y z hy hgen

/-- The original degree-two cup map is bijective in every integer degree. -/
theorem localTateNakayama_bijective (n : ℤ) :
    Function.Bijective
      (tateCupTrivialInteger U n 2 (n + 2) rfl (localFundamentalTateClass K L i)) := by
  apply tateCupTrivialInteger_bijective_of_lifted U (localFundamentalTateClass K L i) _ _ _ n
  · intro _ _ _ H _
    exact localLiftedTateH1_isZero K L H
  · intro _ _ _ H _
    let : Fintype (J ⧸ H) := Fintype.ofFinite _
    exact (localLiftedTateH2_restriction_properties K L i H).1
  · intro _ _ _ H _ _
    exact (localLiftedTateH2_restriction_properties K L i H).2

/-- The local arithmetic Tate–Nakayama isomorphism on the original units. -/
def localTateNakayama (n : ℤ) :
    tate (integralTrivialInteger.{v, v} Gal(L/K)) n ≃ₗ[ℤ] tate U (n + 2) :=
  LinearEquiv.ofBijective
    (tateCupTrivialInteger U n 2 (n + 2) rfl (localFundamentalTateClass K L i))
    (localTateNakayama_bijective K L i n)

/-- The local isomorphism acts by the original cup against the fundamental class. -/
theorem localTateNakayama_apply (n : ℤ) (x : tate (integralTrivialInteger.{v, v} Gal(L/K)) n) :
    localTateNakayama K L i n x =
      tateCupTrivialInteger U n 2 (n + 2) rfl (localFundamentalTateClass K L i) x := rfl

include i in
/-- The original degree-three unit cohomology vanishes by local Tate–Nakayama. -/
theorem localUnitsH3_isZero : IsZero (cohomology U 3) := by
  have h₁ : IsZero (tate (integralTrivialInteger.{v, v} Gal(L/K)) 1) :=
    tateTrivialInteger_one_isZero
  exact (h₁.of_iso (localTateNakayama K L i 1).toModuleIso.symm).of_iso
    (tatePositiveIsoCohomology U 3).symm

end ClassFieldTheory.Brauer
