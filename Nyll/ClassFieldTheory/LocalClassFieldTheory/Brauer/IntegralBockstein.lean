/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Torsion
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.IntegralUnitClass
public import Nyll.GaloisCohomology.ProP.TrivialZModP
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness

/-! # The actual integral Bockstein criterion for strict dimension -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousCohomology TopRep
open ClassFieldTower.Cohomology

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local notation "Z" => trivialIntegralTopRep G
local notation "R" n => trivialIntegralZModPLifted n G

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem integralNsmulHomo_apply (n : ℕ) (x : Z) :
    (n • (𝟙 Z : Z ⟶ Z)) x = n • x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    change (n • (𝟙 Z : Z ⟶ Z)) x + x = _
    rw [ih]

/-- The actual reduction morphism from trivial integers to finite integers. -/
def integralReduction (n : ℕ) : Z ⟶ R n := by
  let X := Z
  let Y := R n
  let : Module ℤ X := X.hV2
  let : Module ℤ Y := Y.hV2
  let f : X →+ Y :=
    AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((Int.castAddHom (ZMod n)).comp AddEquiv.ulift.toAddMonoidHom)
  exact ConcreteCategory.ofHom (C := TopRep.{u} ℤ G) (X := X) (Y := Y) {
    toLinearMap := f.toIntLinearMap
    cont := @continuous_of_discreteTopology X X.hV3
      (trivialIntegralTopRep_discrete G) Y Y.hV3 _
    isIntertwining' := fun _ => rfl }

/-- The coefficient sequence for the integral Bockstein keeps the original
trivial action, multiplication by the modulus, and reduction. -/
def integralCoefficientShortComplex (n : ℕ) : ShortComplex (TopRep.{u} ℤ G) :=
  ShortComplex.mk (n • (𝟙 Z : Z ⟶ Z)) (integralReduction G n) (by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := (Z).ρ) (π₂ := (R n).ρ)
    apply ContinuousLinearMap.ext
    intro x
    change integralReduction G n ((n • (𝟙 Z : Z ⟶ Z)) x) = 0
    rw [integralNsmulHomo_apply]
    apply ULift.ext
    change ((n • (show ULift.{u} ℤ from x).down : ℤ) : ZMod n) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨_, nsmul_eq_mul _ _⟩)

variable [LocallyCompactSpace G]

/-- A nonzero integral modulus supplies an actual short exact sequence of
continuous cochain complexes. -/
theorem integralCoefficientShortExact (n : ℕ) (hn : n ≠ 0) :
    ((integralCoefficientShortComplex G n).map (continuousModuleComplexFunctor G)).ShortExact := by
  let S := integralCoefficientShortComplex G n
  let : DiscreteTopology S.X₂ := trivialIntegralTopRep_discrete G
  let : DiscreteTopology S.X₃ :=
    show @DiscreteTopology (R n) (inferInstance : TopologicalSpace (R n)) from
      (inferInstance : DiscreteTopology (ULift.{u} (ZMod n)))
  apply continuousModuleComplex_shortExact G S
  · intro x y h
    let a : Z := x
    let b : Z := y
    have hab : (n • (𝟙 Z : Z ⟶ Z)) a = (n • (𝟙 Z : Z ⟶ Z)) b := h
    have hnab : n • a = n • b :=
      (integralNsmulHomo_apply G n a).symm.trans (hab.trans (integralNsmulHomo_apply G n b))
    apply ULift.ext
    exact nsmul_right_injective hn (congrArg ULift.down hnab)
  · intro y
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective ((show ULift.{u} (ZMod n) from y).down)
    exact ⟨ULift.up a, ULift.ext ha⟩
  · intro y hy
    have h : ((show ULift.{u} ℤ from y).down : ZMod n) = 0 := congrArg ULift.down hy
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    let b : Z := ULift.up a
    refine ⟨b, (integralNsmulHomo_apply G n b).trans ?_⟩
    apply ULift.ext
    change n • a = _
    rw [nsmul_eq_mul, ha]
  · exact continuous_snd
  · exact continuous_snd

private theorem integralHomology_nsmul_apply (n i : ℕ)
    (x : ((continuousModuleComplexFunctor G).obj Z).homology i) :
    HomologicalComplex.homologyMap
        ((continuousModuleComplexFunctor G).map (n • (𝟙 Z : Z ⟶ Z))) i x = n • x := by
  let F := continuousModuleComplexFunctor G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) i
  have h : F.map (n • (𝟙 Z : Z ⟶ Z)) = n • 𝟙 (F.obj Z) := by
    rw [Functor.map_nsmul]
    exact congrArg (fun f : F.obj Z ⟶ F.obj Z => n • f) (F.map_id Z)
  exact ConcreteCategory.congr_hom h x

private theorem integralBocksteinImage_eq_torsion (n i : ℕ) (hn : n ≠ 0)
    (x : ((continuousModuleComplexFunctor G).obj Z).homology (i + 1)) :
    (∃ y, (integralCoefficientShortExact G n hn).δ i (i + 1) rfl y = x) ↔ n • x = 0 := by
  let S := (integralCoefficientShortComplex G n).map (continuousModuleComplexFunctor G)
  let hS := integralCoefficientShortExact G n hn
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.homology_exact₁ i (i + 1) rfl)
  have hf : HomologicalComplex.homologyMap S.f (i + 1) x = n • x :=
    integralHomology_nsmul_apply G n (i + 1) x
  have h : HomologicalComplex.homologyMap S.f (i + 1) x = 0 ↔
      ∃ y, hS.δ i (i + 1) rfl y = x := hex x
  rw [hf] at h
  exact h.symm

/-- A uniform prime-power annihilator in the preceding modular cohomology
forces the prime-primary part of integral cohomology to vanish when modular
cohomology in the next degree already vanishes. -/
theorem integralPrimaryCohomology_eq_bot_of_uniform_modular_bound (p m i : ℕ) (hp : p ≠ 0)
    (hnext : IsZero (((continuousModuleComplexFunctor G).obj (R(p ^ m))).homology (i + 1)))
    (hprev : ∀ (k : ℕ) (y : ((continuousModuleComplexFunctor G).obj (R(p ^ k))).homology i),
      p ^ m • y = 0) :
    AddCommGroup.primaryComponent (continuousCohomology (i + 1) Z) p = ⊥ := by
  let C := (continuousModuleComplexFunctor G).obj Z
  have hkill (x : C.homology (i + 1))
      (hx : ∃ k : ℕ, p ^ k • x = 0) : p ^ m • x = 0 := by
    obtain ⟨k, hk⟩ := hx
    let hS := integralCoefficientShortExact G (p ^ k) (pow_ne_zero _ hp)
    obtain ⟨y, hy⟩ := (integralBocksteinImage_eq_torsion G (p ^ k) i (pow_ne_zero _ hp) x).mpr hk
    let δ := (hS.δ i (i + 1) (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl)).hom
    have hy' : δ y = x := hy
    have h₁ : p ^ m • x = p ^ m • δ y :=
      congrArg (fun z : C.homology (i + 1) => p ^ m • z) hy'.symm
    have h₂ : δ (p ^ m • y) = p ^ m • δ y := map_nsmul δ (p ^ m) y
    have h₃ : δ (p ^ m • y) = 0 := (congrArg (fun z => δ z) (hprev k y)).trans (map_zero δ)
    exact h₁.trans (h₂.symm.trans h₃)
  apply (AddSubgroup.eq_bot_iff_forall _).mpr
  intro x hx
  let e := continuousModuleHomologyIso G Z (i + 1)
  let S := (integralCoefficientShortComplex G (p ^ m)).map (continuousModuleComplexFunctor G)
  let hS := integralCoefficientShortExact G (p ^ m) (pow_ne_zero _ hp)
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hx
  have hk' : p ^ k • e.inv x = 0 := by rw [← map_nsmul, hk, map_zero]
  have hzero : HomologicalComplex.homologyMap S.g (i + 1) (e.inv x) = 0 :=
    ConcreteCategory.congr_hom
      (hnext.eq_of_tgt (HomologicalComplex.homologyMap S.g (i + 1)) 0) (e.inv x)
  obtain ⟨y, hy⟩ := (ShortComplex.exact_iff_of_hasForget _).mp
    (hS.homology_exact₂ (i + 1)) _ hzero
  change HomologicalComplex.homologyMap S.f (i + 1) y = e.inv x at hy
  rw [show HomologicalComplex.homologyMap S.f (i + 1) y = p ^ m • y from
    integralHomology_nsmul_apply G (p ^ m) (i + 1) y] at hy
  have hy' : p ^ (k + m) • y = 0 := by
    rw [pow_add, ← smul_smul, hy]
    exact hk'
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  exact (hy.symm.trans (hkill y ⟨k + m, hy'⟩)).trans (map_zero e.inv.hom).symm

end ClassFieldTheory.Brauer
