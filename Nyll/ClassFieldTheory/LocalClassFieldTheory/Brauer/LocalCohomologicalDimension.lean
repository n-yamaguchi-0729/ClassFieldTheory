/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.EmbeddedCorestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerEuler
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerVanishing
public import Nyll.GaloisCohomology.ArtinSchreier.AbsoluteCohomologicalVanishing
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteGeneration
public import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv
public import Nyll.GaloisCohomology.Topology.FiniteCoefficientPrimeDevissage
public import Nyll.GaloisCohomology.Topology.OpenConstantField
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Upper cohomological dimension for actual local coefficients -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory CategoryTheory.Limits ContinuousCohomology TopRep LocalFieldTheory
open ClassFieldTower.Cohomology KummerTheory

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)

local instance : LocallyCompactSpace G :=
  inferInstanceAs (LocallyCompactSpace (InfiniteGalois.profiniteGalGrp K Ω))

variable (p : ℕ) [Fact p.Prime]

/-- A primitive root identifies the trivial coefficient with the actual Kummer module. -/
def primitiveKummerTrivialIso {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    trivialIntegralZModPLifted p G ≅ separableMuTopRep K p := by
  let T := trivialIntegralZModPLifted p G
  let M := separableMuTopRep K p
  let : DiscreteTopology T := inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))
  let : DiscreteTopology M := separableMuTopRep_discrete K p
  let n : ℕ+ := ⟨p, (Fact.out : p.Prime).pos⟩
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let hζΩ := hζ.map_of_injective (f := algebraMap K Ω) (algebraMap K Ω).injective
  let hζU := hζΩ.isUnit_unit' (Fact.out : p.Prime).ne_zero
  let eR : Additive (rootsOfUnity p Ω) ≃+ M :=
    { toFun := fun x => ⟨Additive.ofMul x.toMul.val, congrArg Additive.ofMul x.toMul.property⟩
      invFun := fun x => Additive.ofMul
        ⟨(show Additive Ωˣ from x.val).toMul, congrArg Additive.toMul x.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let e₀ : ULift.{u} (ZMod p) ≃ₗ[ℤ] ZMod p := ULift.moduleEquiv
  let e₁ := hζU.zmodEquivZPowers.trans
    ((MulEquiv.subgroupCongr hζU.zpowers_eq).toAdditive.trans eR)
  let e : T ≃ₗ[ℤ] M := (e₀.toAddEquiv.trans e₁).toIntLinearEquiv
  have hbase : (primitiveRoots (n : ℕ) K).Nonempty := ⟨ζ, (mem_primitiveRoots n.pos).mpr hζ⟩
  have hact (σ : G) (x : M) : M.ρ σ x = x := by
    apply Subtype.ext
    apply Additive.toMul.injective
    exact nthRootsOfUnity_fixed (K := K) (L := Ω) n
      (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := Ω) n hbase)
      σ (show Additive Ωˣ from x.val).toMul (congrArg Additive.toMul x.property)
  let f : T ⟶ M := ConcreteCategory.ofHom (C := TopRep.{u} ℤ G) (X := T) (Y := M) {
    toLinearMap := e.toLinearMap
    cont := continuous_of_discreteTopology
    isIntertwining' := fun σ => by
      apply ContinuousLinearMap.ext
      intro a
      exact (hact σ (e a)).symm }
  apply discreteCoefficientIsoOfBijective f
  change Function.Bijective (fun x : T => e x)
  exact e.bijective

private theorem trivialH3_isZero_of_primitive {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp : (p : K) ≠ 0) :
    IsZero (((continuousModuleComplexFunctor G).obj
      (trivialIntegralZModPLifted p G)).homology 3) := by
  let n : ℕ+ := ⟨p, (Fact.out : p.Prime).pos⟩
  let F := continuousModuleComplexFunctor G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 3
  exact IsZero.of_iso (continuousModuleComplex_isZero_of_cohomology_eq_zero G
    (separableMuTopRep K p) 3 (localKummerH3_eq_zero K n hp))
    (F.mapIso (primitiveKummerTrivialIso K p hζ))

/-- A finite fixed field realizes its actual open subgroup as an absolute Galois group. -/
def fixedFieldAbsoluteEquiv (H : OpenSubgroup G) (E : IntermediateField K Ω)
    [FiniteDimensional K E] (hE : E.fixingSubgroup = H.toSubgroup) :
    Gal(SeparableClosure E/E) ≃ₜ* ↥(H : Subgroup G) := by
  let : IsSepClosure E Ω := ⟨inferInstance, inferInstance⟩
  let : Algebra E (SeparableClosure E) :=
    (separableClosure E (AlgebraicClosure E)).algebra
  let j := IsSepClosure.equiv E Ω (SeparableClosure E)
  let h : ↥E.fixingSubgroup ≃ₜ* ↥(H : Subgroup G) :=
    { toMulEquiv := MulEquiv.subgroupCongr hE
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val (fun σ => hE ▸ σ.property)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val
        (fun σ => hE.symm ▸ σ.property) }
  exact (embeddedAbsoluteRestrictionEquiv K E j).trans h

private theorem openTrivialH3_isZero_of_primitive {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp : (p : K) ≠ 0) (H : OpenSubgroup G) :
    IsZero (((continuousModuleComplexFunctor ↥(H : Subgroup G)).obj
      (trivialIntegralZModPLifted p ↥(H : Subgroup G))).homology 3) := by
  obtain ⟨E, hfin, hfix, _⟩ := exists_finiteIntermediateField_openSubgroup_equiv_apply H
  let : FiniteDimensional K E := hfin
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let T := trivialIntegralZModPLifted p ↥(H : Subgroup G)
  let e := fixedFieldAbsoluteEquiv K H E hfix
  let V := TopRep.res e.toMonoidHom T
  have hζE : IsPrimitiveRoot (algebraMap K E ζ) p :=
    hζ.map_of_injective (f := algebraMap K E) (algebraMap K E).injective
  have hpE : (p : E) ≠ 0 := by
    have h := (algebraMap K E).injective.ne hp
    simpa only [map_natCast, map_zero] using h
  let G' := Gal(SeparableClosure E/E)
  have hV : IsZero (((continuousModuleComplexFunctor G').obj V).homology 3) :=
    trivialH3_isZero_of_primitive E p hζE hpE
  apply continuousModuleComplex_isZero_of_cohomology_eq_zero _ T 3
  intro x
  apply restriction_equiv_injective e T 3
  exact (cohomology_eq_zero_of_continuousModuleComplex_isZero _ V 3 hV _).trans
    (map_zero (map (e : Gal(SeparableClosure E/E) →ₜ* ↥(H : Subgroup G)) (𝟙 V) 3).hom).symm

/-- When the base contains a primitive p-th root, all actual finite
discrete p-annihilated coefficients have vanishing H³. -/
theorem finiteLocalIntegralH3_isZero_of_primitive {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp : (p : K) ≠ 0)
    (X : TopRep.{u} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (hpX : ∀ x : X, p • x = 0) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology 3) := by
  let : Module ℤ X := X.hV2
  obtain ⟨H, hindex, hρ⟩ := exists_openSubgroup_primeToIndex_pGroup_image ℤ G X hX p
  let F := ↥(H : Subgroup G)
  let : LocallyCompactSpace F := H.isClosed.locallyCompactSpace
  let Y := TopRep.res H.toSubgroup.subtype X
  have hY : Continuous (fun fy : F × Y => Y.ρ fy.1 fy.2) :=
    hX.comp (continuous_subtype_val.prodMap continuous_id)
  have h := continuousModuleHomology_isZero_of_pGroup_image F p 3
    (openTrivialH3_isZero_of_primitive K p hζ hp H) Y hY hpX hρ
  apply continuousModuleComplex_isZero_of_cohomology_eq_zero G X 3
  exact H3_eq_zero_of_primeToIndex_open_restriction X H p hpX hindex
    (cohomology_eq_zero_of_continuousModuleComplex_isZero F Y 3 h)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A finite subextension containing a primitive p-th root has an open
fixing subgroup of index prime to p. -/
theorem exists_primitiveRoot_finite_stage_primeToIndex (hp : (p : K) ≠ 0) :
    ∃ (E : IntermediateField K Ω) (_ : FiniteDimensional K E) (ζ : E),
      IsPrimitiveRoot ζ p ∧ ¬ p ∣ E.fixingSubgroup.index := by
  have hp₀ := (Fact.out : p.Prime)
  let : NeZero (p : Ω) := ⟨by
    have hh := (algebraMap K Ω).injective.ne hp
    simpa only [map_natCast, map_zero] using hh⟩
  let : HasEnoughRootsOfUnity Ω p := IsSepClosed.hasEnoughRootsOfUnity Ω p
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω p
  let E := IntermediateField.adjoin K ({ζ} : Set Ω)
  have hζint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  let : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hζint
  have hpoly : Polynomial.aeval ζ (Polynomial.cyclotomic p K) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hp₀.pos
  have hdeg : Module.finrank K E ≤ p - 1 := by
    rw [IntermediateField.adjoin.finrank hζint, ← Nat.totient_prime hp₀,
      ← Polynomial.natDegree_cyclotomic p K]
    exact Polynomial.natDegree_le_natDegree
      (minpoly.min K ζ (Polynomial.cyclotomic.monic p K) hpoly)
  have hidx : E.fixingSubgroup.index = Module.finrank K E :=
    (IntermediateField.finrank_eq_fixingSubgroup_index Ω E).symm
  have hprime : ¬ p ∣ E.fixingSubgroup.index := by
    rw [hidx]
    intro hdvd
    have h := Nat.le_of_dvd (Module.finrank_pos : 0 < Module.finrank K E) hdvd
    exact (Nat.not_le_of_lt (hdeg.trans_lt (Nat.sub_lt hp₀.pos (by decide)))) h
  let Eζ : E := ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
  exact ⟨E, inferInstance, Eζ, IsPrimitiveRoot.of_map_of_injective (f := E.val) hζ E.val.injective,
    hprime⟩

private theorem finiteLocalIntegralH3_isZero_of_invertible (hp : (p : K) ≠ 0)
    (X : TopRep.{u} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (hpX : ∀ x : X, p • x = 0) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology 3) := by
  obtain ⟨E, hE, Eζ, hEζ, hprime⟩ := exists_primitiveRoot_finite_stage_primeToIndex K p hp
  let : FiniteDimensional K E := hE
  let H := stageOpenFixingSubgroup K E
  have hpE : (p : E) ≠ 0 := by
    have h := (algebraMap K E).injective.ne hp
    simpa only [map_natCast, map_zero] using h
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let Y := TopRep.res H.toSubgroup.subtype X
  let e := fixedFieldAbsoluteEquiv K H E rfl
  let G' := Gal(SeparableClosure E/E)
  let V := TopRep.res e.toMonoidHom Y
  let : DiscreteTopology V := inferInstanceAs (DiscreteTopology X)
  let : Finite V := inferInstanceAs (Finite X)
  have hV : Continuous (fun g'v : G' × V => V.ρ g'v.1 g'v.2) :=
    hX.comp ((continuous_subtype_val.comp e.continuous).prodMap continuous_id)
  have hv := finiteLocalIntegralH3_isZero_of_primitive E p hEζ hpE V hV hpX
  apply continuousModuleComplex_isZero_of_cohomology_eq_zero G X 3
  apply H3_eq_zero_of_primeToIndex_open_restriction X H p hpX hprime
  intro x
  apply restriction_equiv_injective e Y 3
  exact (cohomology_eq_zero_of_continuousModuleComplex_isZero G' V 3 hv _).trans
    (map_zero (map (e : G' →ₜ* ↥(H : Subgroup G)) (𝟙 V) 3).hom).symm

/-- For a prime-annihilated finite coefficient, degree three vanishes in all
characteristics. The characteristic prime uses the Artin–Schreier sequence. -/
theorem finiteLocalIntegralH3_isZero_prime
    (X : TopRep.{u} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (hpX : ∀ x : X, p • x = 0) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology 3) := by
  by_cases hp : (p : K) = 0
  · let : CharP K p := (CharP.charP_iff_prime_eq_zero (R := K) (Fact.out : p.Prime)).mpr hp
    let : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
    exact ArtinSchreierTheory.integralCohomology_isZero_of_charP p X hX hpX 1
  · exact finiteLocalIntegralH3_isZero_of_invertible K p hp X hX hpX

/-- Vanishing of degree three for all finite discrete local coefficients. -/
theorem finiteLocalIntegralH3_isZero (X : TopRep.{u} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology 3) := by
  apply continuousModuleHomology_isZero_of_prime_coefficients G 3 ?_ X hX
  intro q hq Y hfin hdisc hY hqY
  exact finiteLocalIntegralH3_isZero_prime K q Y hY hqY

/-- The actual local cohomology vanishes above degree two for all discrete
coefficients annihilated by a nonzero integer. -/
theorem boundedLocalIntegralCohomology_isZero (X : TopRep.{u} ℤ G) [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (m : ℤ) (hm₀ : m ≠ 0) (hm : ∀ x : X, m • x = 0) (n : ℕ) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology (n + 3)) := by
  have h (Y : TopRep.{u} ℤ G) [DiscreteTopology Y]
      (hY : Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2)) (hmY : ∀ y : Y, m • y = 0) :
      IsZero (((continuousModuleComplexFunctor G).obj Y).homology 3) := by
    apply continuousModule_isZero_of_finite_coefficients G Y hY m hm₀ hmY 2
    intro V hfin hdisc hV _hmV
    exact finiteLocalIntegralH3_isZero K V hV
  have hn : 2 + n + 1 = n + 3 := by omega
  simpa only [hn] using continuousModule_isZero_of_fixed_positive_degree G X 2 m h hX hm n

/-- The upper dimension bound uses all actual discrete torsion coefficients. -/
theorem torsionLocalIntegralCohomology_isZero (X : TopRep.{u} ℤ G) [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (ht : Module.IsTorsion ℤ X) (n : ℕ) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology (n + 3)) := by
  apply continuousModule_isZero_of_finite_torsion_coefficients G X hX ht (n + 2)
  intro Y hfin hdisc hY
  let m := Nat.card Y
  have hm₀ : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr Nat.card_pos.ne'
  have hm (y : Y) : (m : ℤ) • y = 0 := (natCast_zsmul y m).trans card_nsmul_eq_zero'
  exact boundedLocalIntegralCohomology_isZero K Y hY m hm₀ hm n

/-- The same upper bound on the original absolute Galois group of mathlib. -/
theorem torsionAbsoluteLocalIntegralCohomology_isZero
    (X : TopRep.{u} ℤ (Field.absoluteGaloisGroup K)) [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup K × X => X.ρ gx.1 gx.2))
    (ht : Module.IsTorsion ℤ X) (n : ℕ) :
    IsZero (((continuousModuleComplexFunctor
      (Field.absoluteGaloisGroup K)).obj X).homology (n + 3)) := by
  let e : G ≃ₜ* Field.absoluteGaloisGroup K :=
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv K).symm
  let Y := TopRep.res e.toMonoidHom X
  let : DiscreteTopology Y := inferInstanceAs (DiscreteTopology X)
  have hY : Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) :=
    hX.comp (e.continuous.prodMap continuous_id)
  have h := torsionLocalIntegralCohomology_isZero K Y hY ht n
  apply continuousModuleComplex_isZero_of_cohomology_eq_zero (Field.absoluteGaloisGroup K) X (n + 3)
  intro x
  let r : G →ₜ* Field.absoluteGaloisGroup K := ContinuousMonoidHom.toContinuousMonoidHom e
  let f := (map (X := X) (Y := Y) r (𝟙 Y) (n + 3)).hom.toLinearMap.toAddMonoidHom
  have hzero : f x = 0 := cohomology_eq_zero_of_continuousModuleComplex_isZero G Y (n + 3) h _
  exact restriction_equiv_injective e X (n + 3) (hzero.trans (map_zero f).symm)

/-- At an invertible prime, a finite discrete p-torsion coefficient detects
the lower dimension bound in degree two. -/
theorem exists_local_prime_annihilated_H2_ne_zero (hp : (p : K) ≠ 0) :
    ∃ X : TopRep.{u} ℤ G, Finite X ∧ DiscreteTopology X ∧
      Continuous (fun gx : G × X => X.ρ gx.1 gx.2) ∧ (∀ x : X, p • x = 0) ∧
      ∃ x : continuousCohomology 2 X, x ≠ 0 := by
  let hp₀ := (Fact.out : p.Prime)
  let n : ℕ+ := ⟨p, hp₀.pos⟩
  let : NeZero p := ⟨hp₀.ne_zero⟩
  refine ⟨separableMuTopRep K p, ?_, inferInstance, separableMuTopRep_action_continuous K p,
    separableMuTopRep_nsmul_eq_zero K p, exists_localKummerH2_ne_zero K n hp hp₀.one_lt⟩
  exact inferInstanceAs (Finite (rootsOfUnity p Ω))

end ClassFieldTheory.Brauer
