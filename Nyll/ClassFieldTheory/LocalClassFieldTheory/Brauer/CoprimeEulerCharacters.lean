/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.EmbeddedCorestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.EmbeddedKummerTrace
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerConjugation
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateDualExactness
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairing
public import Nyll.GaloisCohomology.Topology.ContinuousCharacterDuality
public import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv
public import Mathlib.Tactic.Group

/-! # The degree-one characters at an actual coprime Galois stage -/

@[expose] public section

open CategoryTheory ContinuousCohomology KummerTheory TopRep

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

attribute [local instance] stageSeparableClosureAlgebra

/-- The map of a continuous group equivalence and a coefficient isomorphism,
as an additive equivalence on the same cohomology groups. -/
def groupEquivCohomologyAddEquiv {Γ₀ Γ₁ : Type u} [Group Γ₀] [Group Γ₁]
    [TopologicalSpace Γ₀] [TopologicalSpace Γ₁] [IsTopologicalGroup Γ₀] [IsTopologicalGroup Γ₁]
    (r : Γ₁ ≃ₜ* Γ₀) {A : TopRep.{u} ℤ Γ₀} {B : TopRep.{u} ℤ Γ₁}
    (a : TopRep.res r.toMonoidHom A ≅ B) (d : ℕ) :
    continuousCohomology d A ≃+ continuousCohomology d B :=
  AddEquiv.ofBijective (map (r : Γ₁ →ₜ* Γ₀) a.hom d).hom.toLinearMap.toAddMonoidHom
    (map_bijective_of_groupEquiv r a d)

private theorem groupEquivCohomologyAddEquiv_π {Γ₀ Γ₁ : Type u} [Group Γ₀] [Group Γ₁]
    [TopologicalSpace Γ₀] [TopologicalSpace Γ₁] [IsTopologicalGroup Γ₀] [IsTopologicalGroup Γ₁]
    (r : Γ₁ ≃ₜ* Γ₀) {M : TopRep.{u} ℤ Γ₀} {N : TopRep.{u} ℤ Γ₁}
    (a : TopRep.res r.toMonoidHom M ≅ N) (d : ℕ) (z : cocycles M d) :
    groupEquivCohomologyAddEquiv r a d (π M d z) =
      π N d (cocyclesMap (r : Γ₁ →ₜ* Γ₀) a.hom d z) :=
  ConcreteCategory.congr_hom (π_map (r : Γ₁ →ₜ* Γ₀) a.hom d) z

/-- The character description after transport along an actual group and coefficient equivalence. -/
def transportedTrivialH1CharacterEquiv {G J : Type u} [Group G] [Group J]
    [TopologicalSpace G] [TopologicalSpace J] [IsTopologicalGroup G] [IsTopologicalGroup J]
    [CompactSpace J] {X : TopRep.{u} ℤ G} {Y : TopRep.{u} ℤ J}
    (r : J ≃ₜ* G) (μ : TopRep.res r.toMonoidHom X ≅ Y) (p : ℕ) [Fact p.Prime]
    (hY : ∀ g : J, ∀ a : Y, Y.ρ g a = a) (hpY : ∀ a : Y, p • a = 0) :
    continuousCohomology 1 X ≃+ Additive (J →ₜ* Multiplicative Y) :=
  (groupEquivCohomologyAddEquiv r μ 1).trans (trivialH1ContinuousCharacterEquiv Y hY p hpY)

/-- The crossed homomorphism of a mapped cocycle uses the original group and coefficient maps. -/
theorem crossedHomOfCocycle_map_apply {G J : Type u} [Group G] [Group J]
    [TopologicalSpace G] [TopologicalSpace J] [IsTopologicalGroup G] [IsTopologicalGroup J]
    [LocallyCompactSpace G] [LocallyCompactSpace J] {X : TopRep.{u} ℤ G} {Y : TopRep.{u} ℤ J}
    (r : J →ₜ* G) (φ : TopRep.res r.toMonoidHom X ⟶ Y) (z : cocycles X 1) (h : J) :
    (crossedHomOfCocycle Y (cocyclesMap r φ 1 z)).toFun h =
      φ ((crossedHomOfCocycle X z).toFun (r h)) := by
  change ((homogeneousCochains Y).iCycles 1 (cocyclesMap r φ 1 z)).val 1 h =
    φ (((homogeneousCochains X).iCycles 1 z).val 1 (r h))
  let ev (g : G) := φ (((homogeneousCochains X).iCycles 1 z).val g (r h))
  have hpoint :
      ((homogeneousCochains Y).iCycles 1 (cocyclesMap r φ 1 z)).val 1 h = ev (r 1) := by
    change resolutionTupleHomeomorph J Y 2
      ((homogeneousCochains Y).iCycles 1 (cocyclesMap r φ 1 z)).val ![1, h] = _
    rw [cochainOfMappedCocycle, resolutionTupleHomeomorph_cochainsMap]
    rfl
  exact hpoint.trans (congrArg ev r.map_one)

/-- The transported character evaluates an actual degree-one cocycle at the same element. -/
theorem transportedTrivialH1Character_π_apply {G J : Type u} [Group G] [Group J]
    [TopologicalSpace G] [TopologicalSpace J] [IsTopologicalGroup G] [IsTopologicalGroup J]
    [LocallyCompactSpace G] [CompactSpace J] {X : TopRep.{u} ℤ G} {Y : TopRep.{u} ℤ J}
    (r : J ≃ₜ* G) (μ : TopRep.res r.toMonoidHom X ≅ Y) (p : ℕ) [Fact p.Prime]
    (hY : ∀ g : J, ∀ a : Y, Y.ρ g a = a) (hpY : ∀ a : Y, p • a = 0)
    (z : cocycles X 1) (h : J) :
    ((transportedTrivialH1CharacterEquiv r μ p hY hpY (π X 1 z)).toMul h).toAdd =
      μ.hom ((crossedHomOfCocycle X z).toFun (r h)) := by
  let r₀ : J →ₜ* G := r
  let φ : TopRep.res r₀.toMonoidHom X ⟶ Y := μ.hom
  let χ := trivialH1ContinuousCharacterEquiv Y hY p hpY
  calc
    _ = ((χ (π Y 1 (cocyclesMap r₀ φ 1 z))).toMul h).toAdd :=
      congrArg (fun y => ((χ y).toMul h).toAdd) (groupEquivCohomologyAddEquiv_π r μ 1 z)
    _ = (crossedHomOfCocycle Y (cocyclesMap r₀ φ 1 z)).toFun h :=
      trivialH1ContinuousCharacterEquiv_π_apply Y hY p hpY (cocyclesMap r₀ φ 1 z) h
    _ = _ := crossedHomOfCocycle_map_apply r₀ φ z h

variable (K : Type u) [Field K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (j : SeparableClosure K ≃ₐ[E] SeparableClosure E)

local notation "Ω" => SeparableClosure K
local notation "ΓK" => Gal(Ω/K)
local notation "S" => stageOpenFixingSubgroup K E.toIntermediateField
local notation "I" => Subtype (fun g : ΓK => g ∈ OpenSubgroup.toSubgroup S)
local notation "e" => embeddedAbsoluteRestrictionEquiv K E.toIntermediateField j

local instance stageOpenFixingSubgroup_normal : (S : Subgroup ΓK).Normal :=
  IsGalois.fixingSubgroup_normal_of_isGalois E.toIntermediateField

/-- The ambient automorphism conjugated by the actual comparison of closures. -/
def stageClosureAutomorphism (g : ΓK) : SeparableClosure E ≃+* SeparableClosure E :=
  j.symm.toRingEquiv.trans (g.toRingEquiv.trans j.toRingEquiv)

theorem stageClosureAutomorphism_algebraMap (g : ΓK) (x : E) :
    stageClosureAutomorphism K E j g (algebraMap E (SeparableClosure E) x) =
      algebraMap E (SeparableClosure E) (finiteGaloisRestriction E g x) := by
  change j (g (j.symm (algebraMap E (SeparableClosure E) x))) = _
  exact (congrArg (fun y => j (g y)) (j.symm.commutes x)).trans
    ((congrArg j (finiteGaloisRestriction_commutes E g x).symm).trans
      (j.commutes (finiteGaloisRestriction E g x)))

/-- The Galois map to the actual open subgroup identifies semilinear
conjugation with conjugation in the original absolute group. -/
theorem embeddedAbsoluteRestrictionEquiv_stageConjugation (g : ΓK)
    (σ : Gal(SeparableClosure E/E)) :
    e (semilinearGaloisConjugateContinuousEquiv (finiteGaloisRestriction E g).toRingEquiv
        (stageClosureAutomorphism K E j g) (stageClosureAutomorphism_algebraMap K E j g) σ) =
      normalOpenConjugate S g (e σ) := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  change j.symm (semilinearGaloisConjugateContinuousEquiv (finiteGaloisRestriction E g).toRingEquiv
    (stageClosureAutomorphism K E j g) (stageClosureAutomorphism_algebraMap K E j g) σ (j x)) =
      g (j.symm (σ (j (g.symm x))))
  rw [semilinearGaloisConjugateContinuousEquiv_apply, semilinearGaloisConjugate_apply]
  change j.symm (j (g (j.symm (σ (j (g.symm (j.symm (j x)))))))) = _
  rw [j.symm_apply_apply, j.symm_apply_apply]

/-- At a Galois stage of degree prime to the coefficient prime, the original
absolute degree-one group is the actual subgroup of invariant characters. -/
def coprimeStageH1CharacterEquiv (A : TopRep.{u} ℤ ΓK) [DiscreteTopology A]
    (p : ℕ) [Fact p.Prime] (hpA : ∀ a : A, p • a = 0)
    (hdeg : ¬ p ∣ Module.finrank K E) (hfix : ∀ (g : I) (a : A), A.ρ (g : ΓK) a = a) :
    continuousCohomology 1 A ≃+ normalOpenInvariantCharacters A S :=
  normalOpenH1RestrictionEquiv A S hfix p hpA (by
    change ¬ p ∣ E.toIntermediateField.fixingSubgroup.index
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index Ω E.toIntermediateField]
    exact hdeg)

section KummerCharacters

variable (p : ℕ) [Fact p.Prime]

local notation "n" => (Subtype.mk p (Nat.Prime.pos (Fact.out : p.Prime)) : ℕ+)
local notation "Mu" => separableMuTopRep K p
local notation "ME" => separableMuTopRep E p
local notation "RS" => TopRep.res (Subgroup.subtype (OpenSubgroup.toSubgroup S)) Mu
local notation "PowerClasses" => Eˣ ⧸ MonoidHom.range (powMonoidHom p : Eˣ →* Eˣ)
local notation "StageCharacters" => Additive (I →ₜ* Multiplicative RS)
local notation "stageCharacterEval" =>
  continuousCharacterEval (G := I) (H := I) RS

/-- A primitive root in the finite stage makes the original fixing subgroup
act trivially on the entire separable roots-of-unity coefficient. -/
theorem stageOpenFixingSubgroup_mu_fixed (ζ : E) (hζ : IsPrimitiveRoot ζ p) (h : I) (a : Mu) :
    (Mu).ρ (h : ΓK) a = a := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζ' : IsPrimitiveRoot (ζ : Ω) p :=
    hζ.map_of_injective (f := E.toIntermediateField.val) E.toIntermediateField.val.injective
  let a₀ : Ωˣ := (show Additive Ωˣ from a.val).toMul
  have hp : (a₀ : Ω) ^ p = 1 :=
    congrArg (fun (t : Additive Ωˣ) => (t.toMul : Ω)) a.property
  obtain ⟨i, _, hi⟩ := hζ'.eq_pow_of_pow_eq_one hp
  have hfix : (h : ΓK) (ζ : Ω) = (ζ : Ω) :=
    (IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField (h : ΓK)).mp h.property
      (ζ : Ω) ζ.property
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  change (h : ΓK) (a₀ : Ω) = (a₀ : Ω)
  rw [← hi, map_pow, hfix]

variable (ζ : E) (hζ : IsPrimitiveRoot ζ p) (hn : (p : E) ≠ 0)

/-- The original Kummer coefficient map as an isomorphism over the open subgroup. -/
def embeddedMuCoefficientIso :
    TopRep.res ((e).symm.toMonoidHom) ME ≅ RS :=
  let _ : DiscreteTopology RS := separableMuTopRep_discrete K p
  discreteCoefficientIsoOfBijective (embeddedMuTransport K E.toIntermediateField j p)
    (embeddedMuTransport_bijective K E.toIntermediateField j p)

/-- The H¹ comparison retains the original Kummer cocycle under character evaluation. -/
def embeddedKummerH1CharacterEquivWithEvaluation :
    {q : continuousCohomology 1 ME ≃+ StageCharacters //
      ∀ (z : cocycles ME 1) (h : I), ((q (π ME 1 z)).toMul h).toAdd =
        embeddedMuTransport K E.toIntermediateField j p
          ((crossedHomOfCocycle ME z).toFun ((e).symm h))} := by
  let : LocallyCompactSpace Gal(SeparableClosure E/E) :=
    separableAbsoluteGalois_locallyCompact E.toIntermediateField
  let : CompactSpace I := isCompact_iff_compactSpace.mp (S).isClosed.isCompact
  let r : I ≃ₜ* Gal(SeparableClosure E/E) := (e).symm
  let i : TopRep.res r.toMonoidHom ME ≅ RS := embeddedMuCoefficientIso K E j p
  let hfix := stageOpenFixingSubgroup_mu_fixed K E p ζ hζ
  let hmu := separableMuTopRep_nsmul_eq_zero K p
  refine ⟨transportedTrivialH1CharacterEquiv r i p hfix hmu, ?_⟩
  intro z h
  exact transportedTrivialH1Character_π_apply (X := ME) (Y := RS) r i p hfix hmu z h

/-- The embedded degree-one group as characters of the original fixing subgroup. -/
def embeddedKummerH1CharacterEquiv :
    continuousCohomology 1 ME ≃+ StageCharacters :=
  (embeddedKummerH1CharacterEquivWithEvaluation K E j p ζ hζ).val

/-- Actual Kummer power classes give the continuous characters of the open
fixing subgroup with values in the original base roots of unity. -/
def embeddedKummerCharacterEquiv : Additive PowerClasses ≃+ StageCharacters :=
  let Q := Additive PowerClasses
  let X := continuousCohomology 1 ME
  let k : Q ≃+ X := (separableMuH1EquivPowerClasses E n hn).toAdditive
  k.trans (embeddedKummerH1CharacterEquiv K E j p ζ hζ)

private theorem embeddedKummerH1CharacterEquiv_π_apply (z : cocycles ME 1) (h : I) :
    ((embeddedKummerH1CharacterEquiv K E j p ζ hζ (π ME 1 z)).toMul h).toAdd =
      embeddedMuTransport K E.toIntermediateField j p
        ((crossedHomOfCocycle ME z).toFun ((e).symm h)) :=
  (embeddedKummerH1CharacterEquivWithEvaluation K E j p ζ hζ).property z h

/-- The characters are represented by the same original Kummer roots. -/
theorem embeddedKummerCharacterEquiv_mk_apply (a : Eˣ) (β : unitsRep E)
    (hβ : p • β = baseUnitValue E a) (h : I) :
    stageCharacterEval h (embeddedKummerCharacterEquiv K E j p ζ hζ hn
        (Additive.ofMul (QuotientGroup.mk a))) =
      embeddedMuTransport K E.toIntermediateField j p
        ((rootKummerCrossedHom E p a β hβ).toFun ((e).symm h)) := by
  let c := rootKummerCrossedHom E p a β hβ
  let χ := embeddedKummerH1CharacterEquiv K E j p ζ hζ
  let μ := embeddedMuTransport K E.toIntermediateField j p
  change stageCharacterEval h (χ (separableKummerH1Class E n hn a)) = μ (c.toFun ((e).symm h))
  have ha : separableKummerH1Class E n hn a = π ME 1 c.toCocycle :=
    separableKummerH1Class_eq_root E n hn a β hβ
  calc
    _ = stageCharacterEval h (χ (π ME 1 c.toCocycle)) :=
      congrArg (fun x => stageCharacterEval h (χ x)) ha
    _ = μ ((crossedHomOfCocycle ME c.toCocycle).toFun ((e).symm h)) :=
      embeddedKummerH1CharacterEquiv_π_apply K E j p ζ hζ c.toCocycle h
    _ = μ (c.toFun ((e).symm h)) := congrArg μ (crossedHomOfCocycle_toCocycle ME c ((e).symm h))

private theorem embeddedMuTransport_stageConjugation (g : ΓK) (a : ME) :
    embeddedMuTransport K E.toIntermediateField j p
      (separableKummerConjugateRoots E (stageClosureAutomorphism K E j g) n a) =
      (Mu).ρ g (embeddedMuTransport K E.toIntermediateField j p a) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  let a₀ : SeparableClosure E := (show Additive (SeparableClosure E)ˣ from a.val).toMul
  change j.symm (j (g (j.symm a₀))) = g (j.symm a₀)
  exact j.symm_apply_apply _

local notation "stageBaseAut" g:arg => AlgEquiv.toRingEquiv (finiteGaloisRestriction E g)
local notation "stageLift" g:arg => stageClosureAutomorphism K E j g
local notation "stageLiftCommutes" g:arg => stageClosureAutomorphism_algebraMap K E j g
local notation "stageConjugationPullback" g:arg =>
  separableKummerConjugationPullback E (stageBaseAut g) (stageLift g) (stageLiftCommutes g)
local notation "stageConjugationCoefficient" g:arg =>
  separableKummerConjugationCoefficient E (stageBaseAut g) (stageLift g) (stageLiftCommutes g) n

private theorem embeddedKummerConjugationPullback_apply (g : ΓK) (h : I) :
    (stageConjugationPullback g) ((e).symm (normalOpenConjugate S g h)) = (e).symm h := by
  let d := semilinearGaloisConjugateContinuousEquiv (stageBaseAut g) (stageLift g)
    (stageLiftCommutes g)
  have hd : d ((e).symm h) = (e).symm (normalOpenConjugate S g h) := by
    apply (e).injective
    exact (embeddedAbsoluteRestrictionEquiv_stageConjugation K E j g ((e).symm h)).trans
      ((congrArg (normalOpenConjugate S g) ((e).apply_symm_apply h)).trans
        ((e).apply_symm_apply (normalOpenConjugate S g h)).symm)
  exact d.symm_apply_eq.mpr hd.symm

private def embeddedKummerH1ConjugationIdentity (g : ΓK)
    (z : continuousCohomology 1 ME) (h : I) : Prop :=
    stageCharacterEval (normalOpenConjugate S g h)
      (embeddedKummerH1CharacterEquiv K E j p ζ hζ
        (map (stageConjugationPullback g) (stageConjugationCoefficient g) 1 z)) =
    (Mu).ρ g (stageCharacterEval h (embeddedKummerH1CharacterEquiv K E j p ζ hζ z))

private theorem embeddedKummerH1CharacterEquiv_stageConjugation_π (g : ΓK)
    (w : cocycles ME 1) (h : I) :
    embeddedKummerH1ConjugationIdentity K E j p ζ hζ g (π ME 1 w) h := by
  let : LocallyCompactSpace Gal(SeparableClosure E/E) :=
    separableAbsoluteGalois_locallyCompact E.toIntermediateField
  unfold embeddedKummerH1ConjugationIdentity
  let r := stageConjugationPullback g
  let φ := stageConjugationCoefficient g
  let h₀ := normalOpenConjugate S g h
  let s := (e).symm h₀
  let μ := embeddedMuTransport K E.toIntermediateField j p
  let χ := embeddedKummerH1CharacterEquiv K E j p ζ hζ
  have hπ : map r φ 1 (π ME 1 w) = π ME 1 (cocyclesMap r φ 1 w) :=
    ConcreteCategory.congr_hom (π_map r φ 1) w
  change ((χ (map r φ 1 (π ME 1 w))).toMul h₀).toAdd =
    (Mu).ρ g ((χ (π ME 1 w)).toMul h).toAdd
  calc
    _ = ((χ (π ME 1 (cocyclesMap r φ 1 w))).toMul h₀).toAdd :=
      congrArg (fun x => ((χ x).toMul h₀).toAdd) hπ
    _ = μ ((crossedHomOfCocycle ME (cocyclesMap r φ 1 w)).toFun s) :=
      embeddedKummerH1CharacterEquiv_π_apply K E j p ζ hζ (cocyclesMap r φ 1 w) h₀
    _ = μ (φ ((crossedHomOfCocycle ME w).toFun (r s))) :=
      congrArg μ (crossedHomOfCocycle_map_apply r φ w s)
    _ = μ (φ ((crossedHomOfCocycle ME w).toFun ((e).symm h))) :=
      congrArg (fun y => μ (φ ((crossedHomOfCocycle ME w).toFun y)))
        (embeddedKummerConjugationPullback_apply K E j g h)
    _ = (Mu).ρ g (μ ((crossedHomOfCocycle ME w).toFun ((e).symm h))) :=
      embeddedMuTransport_stageConjugation K E j p g _
    _ = _ := congrArg ((Mu).ρ g)
      (embeddedKummerH1CharacterEquiv_π_apply K E j p ζ hζ w h).symm

private theorem embeddedKummerH1CharacterEquiv_stageConjugation (g : ΓK)
    (z : continuousCohomology 1 ME) (h : I) :
    stageCharacterEval (normalOpenConjugate S g h)
      (embeddedKummerH1CharacterEquiv K E j p ζ hζ
        (map (stageConjugationPullback g) (stageConjugationCoefficient g) 1 z)) =
    (Mu).ρ g (stageCharacterEval h (embeddedKummerH1CharacterEquiv K E j p ζ hζ z)) := by
  let P (u : continuousCohomology 1 ME) :=
    embeddedKummerH1ConjugationIdentity K E j p ζ hζ g u h
  have hp : ∀ u, P u := ((π_surjective ME 1).forall (p := P)).mpr
    fun w => embeddedKummerH1CharacterEquiv_stageConjugation_π K E j p ζ hζ g w h
  exact hp z

/-- The Kummer character correspondence intertwines the actual Galois action
on power classes with conjugation on the subgroup and the original root action. -/
theorem embeddedKummerCharacterEquiv_conjugation (g : ΓK) (x : PowerClasses) (h : I) :
    stageCharacterEval (normalOpenConjugate S g h) (embeddedKummerCharacterEquiv K E j p ζ hζ hn
      (Additive.ofMul (separableKummerPowerClassConjugation E (stageBaseAut g) n x))) =
      (Mu).ρ g (stageCharacterEval h (embeddedKummerCharacterEquiv K E j p ζ hζ hn
        (Additive.ofMul x))) := by
  let k := (separableMuH1EquivPowerClasses E n hn).toAdditive
  let χ := embeddedKummerH1CharacterEquiv K E j p ζ hζ
  have hx := separableMuH1EquivPowerClasses_conjugation E
    (stageBaseAut g) (stageLift g) (stageLiftCommutes g) n hn x
  have hχ := embeddedKummerH1CharacterEquiv_stageConjugation K E j p ζ hζ g
    (k (Additive.ofMul x)) h
  exact (congrArg (fun y => stageCharacterEval (normalOpenConjugate S g h) (χ y)) hx.symm).trans hχ

variable (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [Finite A] [DiscreteTopology A]

local notation "D" => discreteLinearDual (R := ℤ) (G := ΓK) A (Mu)
local notation "Chars" => Additive (I →ₜ* Multiplicative (Mu))

local instance powerClassesIntegralModule : Module ℤ (Additive PowerClasses) :=
  @AddCommGroup.toIntModule (Additive PowerClasses)
    (@Additive.addCommGroup PowerClasses (QuotientGroup.Quotient.commGroup _))

local instance stageCharacterIntegralModule : Module ℤ Chars :=
  AddCommGroup.toIntModule _

/-- The actual linear maps from the twisted dual into finite-stage power
classes, equivariant for the prescribed actions. -/
def coprimeKummerPowerClassMaps : Set (D →ₗ[ℤ] Additive PowerClasses) :=
  {f | ∀ (g : ΓK) (l : D), f ((D).ρ g l) = Additive.ofMul
    (separableKummerPowerClassConjugation E (finiteGaloisRestriction E g).toRingEquiv n
      (f l).toMul)}

/-- Conjugating an open subgroup element back by the original element is the identity. -/
theorem normalOpenConjugate_inverse (g : ΓK) (h : I) :
    normalOpenConjugate S g (normalOpenConjugate S g⁻¹ h) = h := by
  apply Subtype.ext
  change g * (g⁻¹ * (h : ΓK) * (g⁻¹)⁻¹) * g⁻¹ = (h : ΓK)
  group

/-- Actual coprime Galois-stage degree one is the Hom into power classes
from the original Tate dual. -/
def coprimeStageH1KummerPowerClassEquiv (hnK : (p : K) ≠ 0)
    (hA : ∀ a : A, p • a = 0) (hdeg : ¬p ∣ Module.finrank K E)
    (hfix : ∀ (h : I) (a : A), A.ρ (h : ΓK) a = a) :
    continuousCohomology 1 A ≃ coprimeKummerPowerClassMaps K E p A := by
  let : Finite Mu := separableMuTopRep_finite K n hnK
  let hbid := separableMu_bidual_bijective K n hnK A hA
  let Φadd : Additive PowerClasses ≃+ Chars := embeddedKummerCharacterEquiv K E j p ζ hζ hn
  let Φ : Additive PowerClasses ≃ₗ[ℤ] Chars :=
    @AddEquiv.toIntLinearEquiv (Additive PowerClasses) Chars
      (@Additive.addCommGroup PowerClasses (QuotientGroup.Quotient.commGroup _))
      (inferInstance : AddCommGroup Chars) inferInstance inferInstance Φadd
  let t : (D →ₗ[ℤ] Chars) ≃ (D →ₗ[ℤ] Additive PowerClasses) :=
    (LinearEquiv.congrRight Φ.symm).toEquiv
  have hS : ¬p ∣ (S).toSubgroup.index := by
    change ¬p ∣ E.toIntermediateField.fixingSubgroup.index
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index Ω E.toIntermediateField]
    exact hdeg
  refine (normalOpenH1DualCharacterEquiv A Mu hbid S p hA hS hfix).trans
    (t.subtypeEquiv fun f => ?_)
  change f ∈ normalOpenDualCharacterMaps A Mu S ↔ t f ∈ coprimeKummerPowerClassMaps K E p A
  have hΦ (l : D) : Φ ((t f) l) = f l := Φ.apply_symm_apply (f l)
  let κ (g : ΓK) (x : Additive PowerClasses) : Additive PowerClasses :=
    Additive.ofMul (separableKummerPowerClassConjugation E (stageBaseAut g) n x.toMul)
  let eval (h : I) (χ : Chars) : Mu := stageCharacterEval h χ
  have hκ (g : ΓK) (l : D) (h : I) :
      eval (normalOpenConjugate S g h) (Φ (κ g ((t f) l))) =
        (Mu).ρ g (eval h (f l)) :=
    (embeddedKummerCharacterEquiv_conjugation K E j p ζ hζ hn g ((t f) l).toMul h).trans
      (congrArg ((Mu).ρ g) (congrArg (eval h) (hΦ l)))
  constructor
  · intro hf g l
    change (t f) ((D).ρ g l) = κ g ((t f) l)
    apply Φ.injective
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro h
    let h₀ := normalOpenConjugate S g⁻¹ h
    have hh : normalOpenConjugate S g h₀ = h := normalOpenConjugate_inverse K E g h
    apply Multiplicative.toAdd.injective
    change eval h (Φ ((t f) ((D).ρ g l))) = eval h (Φ (κ g ((t f) l)))
    calc
      _ = eval h (f ((D).ρ g l)) := congrArg (eval h) (hΦ ((D).ρ g l))
      _ = eval (normalOpenConjugate S g h₀) (f ((D).ρ g l)) :=
        congrArg (fun y => eval y (f ((D).ρ g l))) hh.symm
      _ = (Mu).ρ g (eval h₀ (f l)) := hf g l h₀
      _ = eval (normalOpenConjugate S g h₀) (Φ (κ g ((t f) l))) := (hκ g l h₀).symm
      _ = _ := congrArg (fun y => eval y (Φ (κ g ((t f) l)))) hh
  · intro hf g l h
    have hκf : (t f) ((D).ρ g l) = κ g ((t f) l) := hf g l
    let h₀ := normalOpenConjugate S g h
    change eval h₀ (f ((D).ρ g l)) = (Mu).ρ g (eval h (f l))
    calc
      _ = eval h₀ (Φ ((t f) ((D).ρ g l))) := congrArg (eval h₀) (hΦ ((D).ρ g l)).symm
      _ = eval h₀ (Φ (κ g ((t f) l))) := congrArg (fun y => eval h₀ (Φ y)) hκf
      _ = _ := hκ g l h

end KummerCharacters

end ClassFieldTheory.Brauer
