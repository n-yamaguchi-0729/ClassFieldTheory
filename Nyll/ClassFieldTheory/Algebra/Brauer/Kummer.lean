/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Cohomology
public import Nyll.ClassFieldTheory.Algebra.Brauer.UnitsInvariants
public import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousHilbert90
public import Nyll.GaloisCohomology.Topology.ContinuousH0Naturality
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousCrossedHom
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness
public import Nyll.GaloisCohomology.Topology.InvariantCoefficientSubrepresentation
public import Mathlib.FieldTheory.Galois.Profinite

/-! # The continuous Kummer sequence on separable-closure units -/

@[expose] public section

open scoped Topology
open CategoryTheory CategoryTheory.Limits ContinuousCohomology ContRepresentation TopRep

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)
local notation "U" => unitsRep K

local instance : LocallyCompactSpace G := by
  let hCompact : CompactSpace G := (InfiniteGalois.continuousMulEquivToLimit K Ω).symm.compactSpace
  let : T2Space G := krullTopology_t2
  exact LocallyCompactSpace.of_hasBasis
    (fun g => hCompact.isCompact_univ.isCompact_isClosed_basis_nhds (x := g) Filter.univ_mem)
    (fun _ _ h => h.2.1)

private theorem separableUnitsCrossedHom_primitive (c : CrossedHom U) :
    ∃ b : U, ∀ σ : G, c.toFun σ = (U).ρ σ b - b := by
  let cMul (σ : G) : Ωˣ := (show Additive Ωˣ from c.toFun σ).toMul
  have hmult : groupCohomology.IsMulCocycle₁ cMul := by
    intro σ τ
    have h := congrArg (Additive.toMul : Additive Ωˣ → Ωˣ) (c.map_mul σ τ)
    change cMul (σ * τ) = cMul σ * (σ • cMul τ) at h
    exact h.trans (mul_comm _ _)
  have hconst : IsLocallyConstant cMul :=
    ((IsLocallyConstant.iff_continuous c.toFun).mpr c.continuous_toFun).comp Additive.toMul
  obtain ⟨b, hb⟩ := KummerTheory.noetherHilbert90_of_isLocallyConstant cMul hmult hconst
  let b₀ : U := Additive.ofMul b
  exact ⟨b₀, fun σ => congrArg Additive.ofMul (hb σ).symm⟩

private def homogeneousZeroLift {J : Type u} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (X : TopRep.{u} ℤ J) (hX : Continuous (fun a : J × X => X.ρ a.1 a.2))
    (b₀ : X) : (homogeneousCochains X).X 0 := by
  let f : C(J, X) := ⟨fun σ => X.ρ σ b₀, hX.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨f, ?_⟩
  intro τ
  apply ContinuousMap.ext
  intro σ
  change X.ρ τ (X.ρ (τ⁻¹ * σ) b₀) = X.ρ σ b₀
  have h := DFunLike.congr_fun (map_mul X.ρ τ (τ⁻¹ * σ)) b₀
  rw [mul_inv_cancel_left] at h
  exact h.symm

private theorem homogeneousZeroLift_d_apply {J : Type u} [Group J] [TopologicalSpace J]
    [IsTopologicalGroup J] (X : TopRep.{u} ℤ J)
    (hX : Continuous (fun a : J × X => X.ρ a.1 a.2)) (b₀ : X) (σ τ : J) :
    ((homogeneousCochains X).d 0 1 (homogeneousZeroLift X hX b₀)).val σ τ =
      X.ρ τ b₀ - X.ρ σ b₀ := by
  let t := homogeneousZeroLift X hX b₀
  have hd := congrArg (fun w => w σ τ) (homogeneousCochains.d_apply X 0 t)
  exact hd.trans (by rfl)

private abbrev unitsHomogeneousZeroLift (b₀ : U) : (homogeneousCochains U).X 0 :=
  homogeneousZeroLift U (galoisUnitsRep_action_continuous K Ω) b₀

private theorem unitsCocycle_values (z : cocycles U 1) (σ τ : G) :
    ((homogeneousCochains U).iCycles 1 z).val σ τ =
      (crossedHomOfCocycle U z).toFun τ - (crossedHomOfCocycle U z).toFun σ := by
  let C := homogeneousCochains U
  let z₀ := C.iCycles 1 z
  have h := ConcreteCategory.congr_hom (C.iCycles_d 1 2) z
  have hd := congrArg (fun w => w 1 σ τ) (homogeneousCochains.d_apply U 1 z₀)
  have hz := congrArg (fun w : C.X 2 => w.1 1 σ τ) h
  change (((C.d 1 2).hom z₀).1 1 σ τ) = 0 at hz
  rw [hd] at hz
  simp only [d_succ, d_zero, TopRep.hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ConcreteCategory.hom_ofHom, ContinuousMap.sub_apply] at hz
  exact sub_eq_zero.mp hz

private theorem unitsCocycle_boundary (z : cocycles U 1) (b₀ : U)
    (hc : ∀ σ : G, (crossedHomOfCocycle U z).toFun σ = (U).ρ σ b₀ - b₀) :
    (homogeneousCochains U).d 0 1 (unitsHomogeneousZeroLift K b₀) =
      (homogeneousCochains U).iCycles 1 z := by
  let C := homogeneousCochains U
  let z₀ := C.iCycles 1 z
  let t := unitsHomogeneousZeroLift K b₀
  apply Subtype.ext
  apply ContinuousMap.ext
  intro σ
  apply ContinuousMap.ext
  intro τ
  change ((C.d 0 1).hom t).val σ τ = z₀.val σ τ
  have hd : ((C.d 0 1).hom t).val σ τ = (U).ρ τ b₀ - (U).ρ σ b₀ :=
    homogeneousZeroLift_d_apply U (galoisUnitsRep_action_continuous K Ω) b₀ σ τ
  have hz : z₀.val σ τ =
      (crossedHomOfCocycle U z).toFun τ - (crossedHomOfCocycle U z).toFun σ :=
    unitsCocycle_values K z σ τ
  rw [hd, hz, hc τ, hc σ]
  change (U).ρ τ b₀ - (U).ρ σ b₀ = ((U).ρ τ b₀ - b₀) - ((U).ρ σ b₀ - b₀)
  abel

private theorem homogeneousOneBoundary_π {J : Type u} [Group J] [TopologicalSpace J]
    [IsTopologicalGroup J] (X : TopRep.{u} ℤ J) (z : cocycles X 1)
    (t : (homogeneousCochains X).X 0)
    (ht : (homogeneousCochains X).d 0 1 t = (homogeneousCochains X).iCycles 1 z) :
    π X 1 z = 0 := by
  let C := homogeneousCochains X
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  let i := F.map (C.iCycles 1)
  have hi := (ModuleCat.mono_iff_injective i).mp inferInstance
  have hti : C.toCycles 0 1 t = z := hi
    ((ConcreteCategory.congr_hom (C.toCycles_i 0 1) t).trans ht)
  change C.homologyπ 1 z = 0
  rw [← hti]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 0 1) t

/-- Continuous Hilbert 90 for the exact homogeneous cohomology used by the Brauer group. -/
theorem absoluteUnitsH1_eq_zero (x : continuousCohomology 1 U) : x = 0 := by
  obtain ⟨z, rfl⟩ := ContinuousCohomology.π_surjective U 1 x
  obtain ⟨b₀, hc⟩ := separableUnitsCrossedHom_primitive K (crossedHomOfCocycle U z)
  let t := unitsHomogeneousZeroLift K b₀
  exact homogeneousOneBoundary_π U z t (unitsCocycle_boundary K z b₀ hc)

/-- The categorical power map acts by the original scalar multiplication on units. -/
theorem unitsPower_apply (n : ℕ) (x : U) : (n • (𝟙 U : U ⟶ U)) x = n • x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    change (n • (𝟙 U : U ⟶ U)) x + x = n • x + x
    rw [ih]

/-- The original separable units killed by the exponent. -/
def unitsTorsionSubmodule (n : ℕ) : Submodule ℤ U :=
  LinearMap.ker (n • LinearMap.id)

/-- The original Galois action preserves the torsion unit submodule. -/
theorem unitsTorsionSubmodule_invariant (n : ℕ) (σ : G) :
    unitsTorsionSubmodule K n ≤ (unitsTorsionSubmodule K n).comap ((U).ρ σ).toLinearMap := by
  intro z hz
  change n • z = 0 at hz
  change n • (U).ρ σ z = 0
  rw [← map_nsmul, hz, map_zero]

/-- The actual roots of unity in the separable closure with the restricted unit action. -/
def separableMuTopRep (n : ℕ) : TopRep.{u} ℤ G :=
  invariantSubmoduleTopRep ℤ G U (unitsTorsionSubmodule K n) (unitsTorsionSubmodule_invariant K n)

instance separableMuTopRep_discrete (n : ℕ) : DiscreteTopology (separableMuTopRep K n) :=
  invariantSubmoduleTopRep_discrete ℤ G U (unitsTorsionSubmodule K n)
    (unitsTorsionSubmodule_invariant K n)

theorem separableMuTopRep_action_continuous (n : ℕ) :
    Continuous (fun ga : G × separableMuTopRep K n => (separableMuTopRep K n).ρ ga.1 ga.2) :=
  invariantSubmoduleTopRep_action_continuous ℤ G U (unitsTorsionSubmodule K n)
    (unitsTorsionSubmodule_invariant K n) (galoisUnitsRep_action_continuous K Ω)

theorem separableMuTopRep_nsmul_eq_zero (n : ℕ) (x : separableMuTopRep K n) :
    n • x = 0 :=
  Subtype.ext x.property

/-- Inclusion of the original roots of unity into the coefficient units. -/
def separableMuInclusion (n : ℕ) : separableMuTopRep K n ⟶ U :=
  invariantSubmoduleInclusion ℤ G U (unitsTorsionSubmodule K n)
    (unitsTorsionSubmodule_invariant K n)

/-- The original base unit, written additively in the coefficient module. -/
def baseUnitValue (a : Kˣ) : U :=
  (baseUnitInvariant K a).val

/-- The original base unit is fixed by the separable Galois action. -/
theorem baseUnitValue_invariant (a : Kˣ) (σ : G) :
    (U).ρ σ (baseUnitValue K a) = baseUnitValue K a :=
  (baseUnitInvariant K a).property σ

/-- A specified root of the original base unit yields the actual Kummer
crossed homomorphism on separable-closure units. -/
def rootKummerCrossedHom (n : ℕ) (a : Kˣ) (β : U)
    (hβ : n • β = baseUnitValue K a) : CrossedHom (separableMuTopRep K n) := by
  let f (σ : G) : U := (U).ρ σ β - β
  have hf (σ : G) : n • f σ = 0 := by
    dsimp only [f]
    rw [nsmul_sub, ← map_nsmul, hβ, baseUnitValue_invariant, sub_self]
  refine
    { toFun := fun σ => ⟨f σ, hf σ⟩
      continuous_toFun := ((galoisUnitsRep_action_continuous K Ω).comp
        (continuous_id.prodMk continuous_const)).sub continuous_const |>.subtype_mk hf
      map_mul := ?_ }
  intro σ τ
  apply Subtype.ext
  change (U).ρ (σ * τ) β - β = ((U).ρ σ β - β) + (U).ρ σ ((U).ρ τ β - β)
  rw [map_sub]
  have h := congrArg (fun f : U →L[ℤ] U => f β) (map_mul (U).ρ σ τ)
  change (U).ρ (σ * τ) β = (U).ρ σ ((U).ρ τ β) at h
  rw [h]
  abel

/-- The actual continuous Kummer coefficient sequence with the power map. -/
abbrev separableKummerShortComplex (n : ℕ) : ShortComplex (TopRep.{u} ℤ G) :=
  ShortComplex.mk (separableMuInclusion K n) (n • 𝟙 U) (by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    change (n • (𝟙 U : U ⟶ U)) ((separableMuInclusion K n) x) = 0
    rw [unitsPower_apply]
    exact x.property)

/-- Every original separable-closure unit has an nth root when the
positive exponent is nonzero in the field. -/
theorem separableUnits_nsmul_surjective (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    Function.Surjective (fun a : U => (n : ℕ) • a) := by
  let : NeZero ((n : ℕ) : Ω) := ⟨by
    have h := (algebraMap K Ω).injective.ne hn
    simpa only [map_natCast, map_zero] using h⟩
  intro a
  let a' : Ωˣ := (show Additive Ωˣ from a).toMul
  obtain ⟨b, hb⟩ := IsSepClosed.exists_pow_nat_eq (a' : Ω) (n : ℕ)
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.ne_zero] at hb
    exact a'.ne_zero hb.symm
  exact ⟨Additive.ofMul (Units.mk0 b hb0), congrArg Additive.ofMul (Units.ext hb)⟩

/-- For a positive exponent nonzero in the base field, the Kummer sequence
induces a short exact sequence of actual continuous cochain complexes. -/
theorem separableKummerShortExact (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    ((separableKummerShortComplex K n).map (continuousModuleComplexFunctor G)).ShortExact := by
  let S := separableKummerShortComplex K n
  let : DiscreteTopology S.X₂ := by
    change DiscreteTopology U
    infer_instance
  let : DiscreteTopology S.X₃ := by
    change DiscreteTopology U
    infer_instance
  have hU := galoisUnitsRep_action_continuous K Ω
  apply continuousModuleComplex_shortExact G S
  · exact Subtype.val_injective
  · intro a
    change ∃ b : U, (n.val • (𝟙 U : U ⟶ U)) b = a
    obtain ⟨b, hb⟩ := separableUnits_nsmul_surjective K n hn a
    exact ⟨b, (unitsPower_apply K n b).trans hb⟩
  · intro a ha
    let a₀ : U := a
    have h : (n.val • (𝟙 U : U ⟶ U)) a₀ = 0 := ha
    exact ⟨⟨a₀, (unitsPower_apply K n a₀).symm.trans h⟩, rfl⟩
  · exact separableMuTopRep_action_continuous K n
  · exact hU

/-- The map into the actual Brauer group induced by inclusion of the roots of unity. -/
def separableMuH2ToBr (n : ℕ) : continuousCohomology 2 (separableMuTopRep K n) →+ Br K :=
  ((continuousModuleHomologyIso G (separableMuTopRep K n) 2).inv ≫
    HomologicalComplex.homologyMap
      ((continuousModuleComplexFunctor G).map (separableMuInclusion K n)) 2 ≫
    (continuousModuleHomologyIso G U 2).hom).hom.toAddMonoidHom

/-- Kummer inclusion on cohomology is the coefficient map over the identity. -/
theorem separableMuH2ToBr_apply (n : ℕ) (x : continuousCohomology 2 (separableMuTopRep K n)) :
    separableMuH2ToBr K n x =
      ContinuousCohomology.map (ContinuousMonoidHom.id G) (separableMuInclusion K n) 2 x := by
  let X := separableMuTopRep K n
  let e := continuousModuleHomologyIso G X 2
  let i : TopRep.res (ContinuousMonoidHom.id G).toMonoidHom X ⟶ U := separableMuInclusion K n
  have h : separableMuH2ToBr K n x =
      ContinuousCohomology.map (ContinuousMonoidHom.id G) i 2 (e.hom (e.inv x)) :=
    continuousModuleHomologyIso_map_apply (separableMuInclusion K n) 2 (e.inv x)
  exact h.trans (congrArg (ContinuousCohomology.map (ContinuousMonoidHom.id G) i 2)
    (Iso.inv_hom_id_apply e x))

/-- Inclusion of the original Kummer coefficients is literal inclusion
on homogeneous cocycle representatives. -/
theorem separableMuH2ToBr_π (n : ℕ)
    (z : cocycles (separableMuTopRep K n) 2) :
    separableMuH2ToBr K n (π (separableMuTopRep K n) 2 z) =
      π U 2 (cocyclesMap (ContinuousMonoidHom.id G) (separableMuInclusion K n) 2 z) := by
  let i : TopRep.res (ContinuousMonoidHom.id G).toMonoidHom (separableMuTopRep K n) ⟶ U :=
    separableMuInclusion K n
  exact (separableMuH2ToBr_apply K n _).trans
    (ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.id G) i 2) z)

/-- The power map acts on the actual continuous module cohomology by its exponent. -/
theorem moduleHomology_power_apply (n i : ℕ)
    (x : ((continuousModuleComplexFunctor G).obj U).homology i) :
    HomologicalComplex.homologyMap
        ((continuousModuleComplexFunctor G).map (n • (𝟙 U : U ⟶ U))) i x = n • x := by
  let F := continuousModuleComplexFunctor G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) i
  have h : F.map (n • (𝟙 U : U ⟶ U)) = n • 𝟙 (F.obj U) := by
    rw [Functor.map_nsmul, F.map_id U]
  exact ConcreteCategory.congr_hom h x

/-- The original root of unity in the base field gives a fixed coefficient. -/
def baseRootsOfUnityInvariant (n : ℕ) (a : (powMonoidHom n : Kˣ →* Kˣ).ker) :
    (separableMuTopRep K n).invariants := by
  let z := baseUnitInvariant K a.val
  have hpow : n • z.val = 0 := by
    have h : baseUnitsInSeparableClosure K a.val ^ n = 1 := by
      rw [← map_pow, show a.val ^ n = 1 from a.property, map_one]
    exact congrArg Additive.ofMul h
  exact ⟨⟨z.val, hpow⟩, fun σ => Subtype.ext (z.property σ)⟩

/-- Degree zero for the original Kummer coefficients consists of the
roots of unity in the base field. -/
def separableMuH0EquivBaseRoots (n : ℕ) :
    continuousCohomology 0 (separableMuTopRep K n) ≃+
      Additive ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  let V := separableMuTopRep K n
  let e := zeroIso V
  let f : Additive ((powMonoidHom n : Kˣ →* Kˣ).ker) →+ V.invariants :=
    { toFun := fun a => baseRootsOfUnityInvariant K n a.toMul
      map_zero' := Subtype.ext (Subtype.ext
        (congrArg Additive.ofMul (map_one (baseUnitsInSeparableClosure K))))
      map_add' := fun a b => Subtype.ext (Subtype.ext
        (congrArg Additive.ofMul
          (map_mul (baseUnitsInSeparableClosure K) a.toMul.val b.toMul.val))) }
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply Additive.toMul.injective
      apply Subtype.ext
      apply baseUnitsInSeparableClosure_injective K
      exact congrArg (fun z : V.invariants => (show Additive Ωˣ from z.val.val).toMul) h
    · intro z
      let u : (U).invariants := ⟨z.val.val, fun σ => congrArg Subtype.val (z.property σ)⟩
      obtain ⟨a, ha⟩ := (baseUnitsInvariantEquiv K).surjective u
      have hau : baseUnitsInSeparableClosure K a.toMul = (show Additive Ωˣ from z.val.val).toMul :=
        congrArg (fun b : (U).invariants => (show Additive Ωˣ from b.val).toMul) ha
      have hp : a.toMul ^ n = 1 := by
        apply baseUnitsInSeparableClosure_injective K
        rw [map_pow, hau, map_one]
        exact congrArg Additive.toMul z.val.property
      exact ⟨Additive.ofMul ⟨a.toMul, hp⟩, Subtype.ext (Subtype.ext (congrArg Additive.ofMul hau))⟩
  exact (AddEquiv.ofBijective e.hom.hom.toLinearMap.toAddMonoidHom
    (ConcreteCategory.bijective_of_isIso e.hom)).trans (AddEquiv.ofBijective f hf).symm

/-- The continuous Kummer connecting morphism identifies degree one for the
original separable roots-of-unity representation with the base power classes. -/
def separableMuH1EquivPowerClasses (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ≃*
      Multiplicative (continuousCohomology 1 (separableMuTopRep K n)) := by
  let V := separableMuTopRep K n
  let S := (separableKummerShortComplex K n).map (continuousModuleComplexFunctor G)
  let hS := separableKummerShortExact K n hn
  let e₀ := continuousModuleHomologyIso G U 0
  let e₁ := continuousModuleHomologyIso G V 1
  let δ := hS.δ 0 1 rfl
  let u : Additive Kˣ ≃+ S.X₃.homology 0 := (separableUnitsH0EquivBaseUnits K).symm.trans
    (AddEquiv.ofBijective e₀.inv.hom.toAddMonoidHom (ConcreteCategory.bijective_of_isIso e₀.inv))
  let f : Kˣ →* Multiplicative (continuousCohomology 1 V) :=
    (e₁.hom.hom.toAddMonoidHom.comp (δ.hom.toAddMonoidHom.comp u.toAddMonoidHom)).toMultiplicative
  have hzero : IsZero (S.X₂.homology 1) :=
    continuousModuleComplex_isZero_of_cohomology_eq_zero G U 1 (absoluteUnitsH1_eq_zero K)
  have hδ : Function.Surjective δ :=
    (ModuleCat.epi_iff_surjective δ).mp (hS.epi_δ 0 1 rfl hzero)
  have hf : Function.Surjective f :=
    (ConcreteCategory.bijective_of_isIso e₁.hom).2.comp (hδ.comp u.surjective)
  have hpower (x : S.X₂.homology 0) :
      HomologicalComplex.homologyMap S.g 0 x = (n : ℕ) • x :=
    moduleHomology_power_apply K n 0 x
  have hker : f.ker = (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
    ext a
    change e₁.hom (δ (u (Additive.ofMul a))) = 0 ↔ ∃ b : Kˣ, b ^ (n : ℕ) = a
    constructor
    · intro ha
      have ha' : δ (u (Additive.ofMul a)) = 0 := (ConcreteCategory.bijective_of_isIso e₁.hom).1
        (ha.trans (map_zero e₁.hom.hom).symm)
      obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
        (hS.homology_exact₃ 0 1 rfl) _ ha'
      change HomologicalComplex.homologyMap S.g 0 y = u (Additive.ofMul a) at hy
      obtain ⟨b, rfl⟩ := u.surjective y
      let b₀ : S.X₂.homology 0 := u b
      have hp : (n : ℕ) • u b = u (Additive.ofMul a) := (hpower b₀).symm.trans hy
      exact ⟨b.toMul, congrArg Additive.toMul (u.injective ((map_nsmul u (n : ℕ) b).trans hp))⟩
    · rintro ⟨b, rfl⟩
      change e₁.hom (δ (u ((n : ℕ) • Additive.ofMul b))) = 0
      let b₀ : S.X₂.homology 0 := u (Additive.ofMul b)
      have hp : u ((n : ℕ) • Additive.ofMul b) = HomologicalComplex.homologyMap S.g 0 b₀ :=
        (map_nsmul u (n : ℕ) (Additive.ofMul b)).trans (hpower b₀).symm
      have h : δ (HomologicalComplex.homologyMap S.g 0 b₀) = 0 :=
        ConcreteCategory.congr_hom (hS.comp_δ 0 1 rfl) b₀
      exact (congrArg (fun z : S.X₃.homology 0 => e₁.hom (δ z)) hp).trans
        ((congrArg e₁.hom h).trans (map_zero e₁.hom.hom))
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The canonical Kummer class of a base unit on the original continuous
separable roots-of-unity coefficients. -/
def separableKummerH1Class (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (a : Kˣ) :
    continuousCohomology 1 (separableMuTopRep K n) :=
  Multiplicative.toAdd (separableMuH1EquivPowerClasses K n hn (QuotientGroup.mk a))

theorem separableKummerH1Class_eq_connecting (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (a : Kˣ) :
    separableKummerH1Class K n hn a =
      discreteCoefficientConnecting (separableKummerShortComplex K n)
        (separableKummerShortExact K n hn) 0
        ((separableUnitsH0EquivBaseUnits K).symm (Additive.ofMul a)) := by
  unfold separableKummerH1Class separableMuH1EquivPowerClasses
  dsimp only [MulEquiv.trans_apply]
  rw [QuotientGroup.quotientMulEquivOfEq_mk]; rfl

/-- The connecting morphism on the original sequence is represented by
the root cocycle `σ ↦ σ(β) / β`. -/
theorem separableKummerH1Class_eq_root (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (a : Kˣ)
    (β : U) (hβ : (n : ℕ) • β = baseUnitValue K a) :
    separableKummerH1Class K n hn a =
      π (separableMuTopRep K n) 1 (rootKummerCrossedHom K n a β hβ).toCocycle := by
  let S := separableKummerShortComplex K n
  let T := S.map (continuousModuleComplexFunctor G)
  let C := homogeneousCochains U
  let z := fixedCocycleZero U (baseUnitInvariant K a)
  let w := (rootKummerCrossedHom K n a β hβ).toCocycle
  let b : C.X 0 := unitsHomogeneousZeroLift K β
  have hpow : T.g = (n : ℕ) • 𝟙 T.X₂ := by
    change (continuousModuleComplexFunctor G).map ((n : ℕ) • 𝟙 U) =
      (n : ℕ) • 𝟙 ((continuousModuleComplexFunctor G).obj U)
    rw [Functor.map_nsmul, (continuousModuleComplexFunctor G).map_id U]
  have hg : T.g.f 0 b = C.iCycles 0 z := by
    rw [hpow, HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f]
    apply Subtype.ext
    apply ContinuousMap.ext
    intro σ
    change (n : ℕ) • ((U).ρ σ β) = (C.iCycles 0 z).val σ
    rw [← map_nsmul, hβ, baseUnitValue_invariant, fixedCocycleZero_apply]; rfl
  have hf : T.f.f 1 ((homogeneousCochains (separableMuTopRep K n)).iCycles 1 w) =
      T.X₂.d 0 1 b := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro σ
    apply ContinuousMap.ext
    intro τ
    change (((homogeneousCochains (separableMuTopRep K n)).iCycles 1
      (rootKummerCrossedHom K n a β hβ).toCocycle).val σ τ).val = ((C.d 0 1) b).val σ τ
    have hd : ((C.d 0 1) b).val σ τ = (U).ρ τ β - (U).ρ σ β :=
      homogeneousZeroLift_d_apply U (galoisUnitsRep_action_continuous K Ω) β σ τ
    rw [CrossedHom.iCycles_toCocycle, CrossedHom.homogeneous_apply, hd]
    change ((U).ρ τ β - β) - ((U).ρ σ β - β) = (U).ρ τ β - (U).ρ σ β
    abel
  have hz : π U 0 z = (separableUnitsH0EquivBaseUnits K).symm (Additive.ofMul a) := by
    let e := separableUnitsH0EquivBaseUnits K
    apply e.injective
    rw [e.apply_symm_apply]
    change (baseUnitsInvariantEquiv K).symm ((zeroIso U).hom (π U 0 z)) = _
    apply (baseUnitsInvariantEquiv K).injective
    rw [AddEquiv.apply_symm_apply, baseUnitsInvariantEquiv_apply]
    apply Subtype.ext
    rw [zeroIso_hom_π_val, fixedCocycleZero_apply]
  have h := discreteCoefficientConnecting_apply_of_lift S
    (separableKummerShortExact K n hn) 0 z w b hg hf
  rw [hz] at h
  rw [separableKummerH1Class_eq_connecting]
  exact h

/-- Continuous Hilbert 90 makes the degree-two map of the Kummer inclusion faithful. -/
theorem separableMuH2ToBr_injective (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    Function.Injective (separableMuH2ToBr K n) := by
  let e := continuousModuleHomologyIso G (separableMuTopRep K n) 2
  let e' := continuousModuleHomologyIso G U 2
  let S := (separableKummerShortComplex K n).map (continuousModuleComplexFunctor G)
  let hS := separableKummerShortExact K n hn
  have hzero : IsZero (S.X₃.homology 1) :=
    continuousModuleComplex_isZero_of_cohomology_eq_zero G U 1 (absoluteUnitsH1_eq_zero K)
  apply (injective_iff_map_eq_zero (separableMuH2ToBr K n)).mpr
  intro x hx
  have hker : HomologicalComplex.homologyMap S.f 2 (e.inv x) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso e'.hom).1
    exact hx.trans (map_zero e'.hom.hom).symm
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₁ 1 2 rfl) _ hker
  have hδ : hS.δ 1 2 rfl = 0 := hzero.eq_of_src _ _
  change hS.δ 1 2 rfl y = e.inv x at hy
  rw [hδ] at hy
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  exact hy.symm.trans (map_zero e.inv.hom).symm

/-- The actual Kummer inclusion in degree two has image exactly the
exponent-torsion subgroup of the Brauer group. -/
theorem mem_range_separableMuH2ToBr_iff (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (x : Br K) :
    x ∈ (separableMuH2ToBr K n).range ↔ (n : ℕ) • x = 0 := by
  let e := continuousModuleHomologyIso G (separableMuTopRep K n) 2
  let e' := continuousModuleHomologyIso G U 2
  let S := (separableKummerShortComplex K n).map (continuousModuleComplexFunctor G)
  let hS := separableKummerShortExact K n hn
  have hpower (z : S.X₂.homology 2) : HomologicalComplex.homologyMap S.g 2 z = (n : ℕ) • z :=
    moduleHomology_power_apply K n 2 z
  constructor
  · rintro ⟨y, rfl⟩
    have hz := nsmul_continuousCohomology_eq_zero_of_coefficients (separableMuTopRep K n) n
      (separableMuTopRep_nsmul_eq_zero K n) 2 y
    exact (map_nsmul (separableMuH2ToBr K n) (n : ℕ) y).symm.trans
      ((congrArg (separableMuH2ToBr K n) hz).trans (map_zero _))
  · intro hx
    let x₀ : S.X₂.homology 2 := e'.inv x
    have hx' : HomologicalComplex.homologyMap S.g 2 x₀ = 0 :=
      (hpower x₀).trans ((map_nsmul e'.inv.hom (n : ℕ) x).symm.trans
        ((congrArg e'.inv hx).trans (map_zero e'.inv.hom)))
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₂ 2) _ hx'
    have hy₀ : HomologicalComplex.homologyMap S.f 2 y = x₀ := hy
    refine ⟨e.hom y, ?_⟩
    change e'.hom (HomologicalComplex.homologyMap S.f 2 (e.inv (e.hom y))) = x
    exact (congrArg (fun z : S.X₁.homology 2 => e'.hom (HomologicalComplex.homologyMap S.f 2 z))
      (Iso.hom_inv_id_apply e y)).trans ((congrArg e'.hom hy₀).trans (Iso.inv_hom_id_apply e' x))

/-- The `n`-torsion subgroup of the absolute Brauer group. -/
def brTorsion (n : ℕ) : AddSubgroup (Br K) where
  carrier := {x | n • x = 0}
  zero_mem' := nsmul_zero n
  add_mem' {x y} hx hy := by
    change n • x = 0 at hx
    change n • y = 0 at hy
    change n • (x + y) = 0
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' {x} hx := by
    change n • x = 0 at hx
    change n • -x = 0
    rw [smul_neg, hx, neg_zero]

/-- For invertible exponent, Kummer identifies actual continuous roots-of-unity
H² with the corresponding torsion in the absolute Brauer group. -/
def separableMuH2EquivBrTorsion (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    continuousCohomology 2 (separableMuTopRep K n) ≃+ brTorsion K n := by
  let f := (separableMuH2ToBr K n).codRestrict (brTorsion K n) (fun x =>
    (mem_range_separableMuH2ToBr_iff K n hn _).mp ⟨x, rfl⟩)
  apply AddEquiv.ofBijective f
  constructor
  · intro x y h
    exact separableMuH2ToBr_injective K n hn (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy⟩ := (mem_range_separableMuH2ToBr_iff K n hn x).mpr x.property
    exact ⟨y, Subtype.ext hy⟩

/-- Degree three for the original Kummer sequence vanishes when the
separable units have trivial third cohomology and the Brauer power map is onto. -/
theorem separableMuH3_eq_zero_of_units (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hBr : Function.Surjective (fun x : Br K => (n : ℕ) • x))
    (hU : ∀ x : continuousCohomology 3 U, x = 0)
    (x : continuousCohomology 3 (separableMuTopRep K n)) : x = 0 := by
  let e := continuousModuleHomologyIso G (separableMuTopRep K n) 3
  let e₂ := continuousModuleHomologyIso G U 2
  let S := (separableKummerShortComplex K n).map (continuousModuleComplexFunctor G)
  let hS := separableKummerShortExact K n hn
  have hzero : IsZero (S.X₂.homology 3) :=
    continuousModuleComplex_isZero_of_cohomology_eq_zero G U 3 hU
  have hz : HomologicalComplex.homologyMap S.f 3 (e.inv x) = 0 := by
    have h := hzero.eq_of_tgt (HomologicalComplex.homologyMap S.f 3) 0
    exact ConcreteCategory.congr_hom h (e.inv x)
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₁ 2 3 rfl) _ hz
  change hS.δ 2 3 rfl y = e.inv x at hy
  obtain ⟨z, hz⟩ := hBr (e₂.hom y)
  let z₀ := e₂.inv z
  have hy₀ : HomologicalComplex.homologyMap S.g 2 z₀ = y := by
    rw [show HomologicalComplex.homologyMap S.g 2 z₀ = (n : ℕ) • z₀ from
      moduleHomology_power_apply K n 2 z₀]
    apply (ConcreteCategory.bijective_of_isIso e₂.hom).1
    rw [map_nsmul]
    change (n : ℕ) • e₂.hom (e₂.inv z) = e₂.hom y
    exact (congrArg ((n : ℕ) • ·) (Iso.inv_hom_id_apply e₂ z)).trans hz
  have hd := ConcreteCategory.congr_hom (hS.comp_δ 2 3 rfl) z₀
  change hS.δ 2 3 rfl (HomologicalComplex.homologyMap S.g 2 z₀) = 0 at hd
  rw [hy₀, hy] at hd
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  rw [map_zero]
  exact hd

end ClassFieldTheory.Brauer
