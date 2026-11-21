/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.IntegralBockstein
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalCohomologicalDimension
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePerfectness
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.PrimaryRoots

/-! # Reduction of the local integral strict bound to finite Tate duality -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory TopRep ContinuousCohomology LocalFieldTheory ClassFieldTower.Cohomology

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact
  localTateTrivialCoefficient_discrete

universe u

/-- An open subgroup inherits its topological group structure from the ambient group. -/
theorem openSubgroup_subtype_isTopologicalGroup
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : OpenSubgroup G) :
    IsTopologicalGroup ↥U :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (U : Subgroup G).subtype

attribute [local instance] openSubgroup_subtype_isTopologicalGroup

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

local notation "G" => Gal(SeparableClosure K/K)
local notation "T" => fun k => trivialIntegralZModPLifted k G
local notation "Mu" => separableMuTopRep K
local notation "D" => fun k => discreteLinearDual (T k) (Mu k)

private def constantDualInvariantEvaluation (n : ℕ) : (D n).invariants →+ (Mu n).invariants where
  toFun f := ⟨discreteLinearDualMap (T n) (Mu n) f.val (ULift.up 1), fun σ => by
    let evaluate (a : D n) := discreteLinearDualMap (T n) (Mu n) a (ULift.up 1)
    have h := congrArg evaluate (f.property σ)
    have he : evaluate ((D n).ρ σ f.val) = (Mu n).ρ σ (evaluate f.val) :=
      discreteLinearDual_action (T n) (Mu n) σ f.val (ULift.up 1)
    exact he.symm.trans h⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem constantDualInvariantEvaluation_injective (n : ℕ) :
    Function.Injective (constantDualInvariantEvaluation K n) := by
  intro f g h
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (show ULift.{u} (ZMod n) from a).down
  have ha : a = z • (ULift.up (1 : ZMod n) : T n) := by
    apply ULift.ext
    change (show ULift.{u} (ZMod n) from a).down = z • (1 : ZMod n)
    rw [zsmul_eq_mul, mul_one]
    exact hz.symm
  let one : T n := ULift.up (1 : ZMod n)
  let f₀ := discreteLinearDualMap (T n) (Mu n) f.val
  let g₀ := discreteLinearDualMap (T n) (Mu n) g.val
  have hfg : f₀ one = g₀ one := congrArg Subtype.val h
  change f₀ a = g₀ a
  exact ((congrArg f₀ ha).trans (map_zsmul f₀ z one)).trans
    ((congrArg (fun b : Mu n => z • b) hfg).trans
      ((congrArg g₀ ha).trans (map_zsmul g₀ z one)).symm)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem exists_constantDualH0_injection (n : ℕ) :
    ∃ f : continuousCohomology 0 (D n) →+ Additive ((powMonoidHom n : Kˣ →* Kˣ).ker),
      Function.Injective f := by
  let e := zeroIso (D n)
  let e' := zeroIso (Mu n)
  let c := constantDualInvariantEvaluation K n
  let a := separableMuH0EquivBaseRoots K n
  refine ⟨a.toAddMonoidHom.comp (e'.inv.hom.toLinearMap.toAddMonoidHom.comp
    (c.comp e.hom.hom.toLinearMap.toAddMonoidHom)), ?_⟩
  have he := (ConcreteCategory.bijective_of_isIso e.hom).1
  exact a.injective.comp ((ConcreteCategory.bijective_of_isIso e'.inv).1.comp
    ((constantDualInvariantEvaluation_injective K n).comp he))

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
private theorem trivialIntegralPrimaryH3_eq_bot_of_groupEquiv {I J : Type u}
    [Group I] [Group J] [TopologicalSpace I] [TopologicalSpace J]
    [IsTopologicalGroup I] [IsTopologicalGroup J] (e : J ≃ₜ* I)
    (h : AddCommGroup.primaryComponent (continuousCohomology 3 (trivialIntegralTopRep J)) p = ⊥) :
    AddCommGroup.primaryComponent (continuousCohomology 3 (trivialIntegralTopRep I)) p = ⊥ := by
  let A := trivialIntegralTopRep I
  let B := TopRep.res e.toMonoidHom A
  let f := map (e : J →ₜ* I) (𝟙 B) 3
  apply (AddSubgroup.eq_bot_iff_forall _).mpr
  intro x hx
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hx
  have hfx : f x ∈ AddCommGroup.primaryComponent (continuousCohomology 3 B) p := by
    apply AddCommGroup.mem_primaryComponent.mpr
    refine ⟨k, ?_⟩
    change p ^ k • f.hom x = 0
    rw [← map_nsmul, hk, map_zero]
  have hz := (AddSubgroup.eq_bot_iff_forall _).mp h _ hfx
  apply restriction_equiv_injective e A 3
  exact hz.trans (map_zero f.hom).symm

/-- The actual degree-two pairing for constant finite coefficients is the
remaining arithmetic input to the integral strict bound. The annihilator is
uniform because primary roots are finite in the local field. -/
theorem localIntegralPrimaryH3_eq_bot_of_constant_duality (hp : (p : K) ≠ 0)
    (hdual : ∀ (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0),
      Function.Injective (localTatePairingTwoAdjoint K n (T (n : ℕ)) hn)) :
    AddCommGroup.primaryComponent (continuousCohomology 3 (trivialIntegralTopRep G)) p = ⊥ := by
  let hp₀ := (Fact.out : p.Prime)
  obtain ⟨m, hm⟩ := exists_pow_annihilating_localPrimaryRoots K p
  have hpow : p ^ m ≠ 0 := pow_ne_zero _ hp₀.ne_zero
  let : NeZero (p ^ m) := ⟨hpow⟩
  let : Finite (T (p ^ m)) := inferInstanceAs (Finite (ULift.{u} (ZMod (p ^ m))))
  have hnext := finiteLocalIntegralH3_isZero K (T (p ^ m)) continuous_snd
  apply integralPrimaryCohomology_eq_bot_of_uniform_modular_bound G p m 2 hp₀.ne_zero hnext
  intro k x
  let n : ℕ+ := ⟨p ^ k, pow_pos hp₀.pos _⟩
  have hn : ((n : ℕ) : K) ≠ 0 := by
    change ((p ^ k : ℕ) : K) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hp
  let e := continuousModuleHomologyIso G (T (p ^ k)) 2
  have hx : p ^ m • e.hom x = 0 := by
    let adj := localTatePairingTwoAdjoint K n (T (n : ℕ)) hn
    obtain ⟨f, hf⟩ := exists_constantDualH0_injection K (p ^ k)
    have hy (y : continuousCohomology 0 (D (p ^ k))) : p ^ m • y = 0 := by
      let a := (f y).toMul
      have ha : a.val ^ (p ^ k) = 1 := a.property
      apply hf
      rw [map_nsmul, map_zero]
      exact congrArg Additive.ofMul (Subtype.ext (hm k a.val ha))
    apply hdual n hn
    change adj (p ^ m • e.hom x) = adj 0
    apply AddMonoidHom.ext
    intro y
    let evaluate (f : continuousCohomology 0 (D (p ^ k)) →+ ZMod (n : ℕ)) := f y
    calc
      _ = p ^ m • adj (e.hom x) y := congrArg evaluate (map_nsmul adj (p ^ m) (e.hom x))
      _ = adj (e.hom x) (p ^ m • y) := (map_nsmul (adj (e.hom x)) (p ^ m) y).symm
      _ = 0 := (congrArg (adj (e.hom x)) (hy y)).trans (map_zero _)
      _ = _ := (congrArg evaluate (map_zero adj)).symm
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [map_nsmul, map_zero]
  exact hx

/-- The integral primary bound over the actual open subgroups reduces to
the constant degree-two pairing over the finite fixed fields. -/
theorem openLocalIntegralPrimaryH3_eq_bot_of_constant_duality (hp : (p : K) ≠ 0)
    (hdual : ∀ (E : Type u) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] (n : ℕ+) (hn : ((n : ℕ) : E) ≠ 0),
      Function.Injective (localTatePairingTwoAdjoint E n
        (trivialIntegralZModPLifted (n : ℕ) Gal(SeparableClosure E/E)) hn))
    (H : OpenSubgroup G) :
    AddCommGroup.primaryComponent
      (continuousCohomology 3 (trivialIntegralTopRep ↥(H : Subgroup G))) p = ⊥ := by
  obtain ⟨E, hfin, hfix, _⟩ :=
    KummerTheory.exists_finiteIntermediateField_openSubgroup_equiv_apply H
  let : FiniteDimensional K E := hfin
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let G' := Gal(SeparableClosure E/E)
  let e := fixedFieldAbsoluteEquiv K H E hfix
  have hpE : (p : E) ≠ 0 := by
    have h := (algebraMap K E).injective.ne hp
    simpa only [map_natCast, map_zero] using h
  have hE : AddCommGroup.primaryComponent
      (continuousCohomology 3 (trivialIntegralTopRep G')) p = ⊥ :=
    localIntegralPrimaryH3_eq_bot_of_constant_duality E p hpE (hdual E)
  exact trivialIntegralPrimaryH3_eq_bot_of_groupEquiv p e hE

/-- The open-subgroup strict bound on the original absolute Galois group. -/
theorem openAbsoluteLocalIntegralPrimaryH3_eq_bot_of_constant_duality (hp : (p : K) ≠ 0)
    (hdual : ∀ (E : Type u) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] (n : ℕ+) (hn : ((n : ℕ) : E) ≠ 0),
      Function.Injective (localTatePairingTwoAdjoint E n
        (trivialIntegralZModPLifted (n : ℕ) Gal(SeparableClosure E/E)) hn))
    (U : OpenSubgroup (Field.absoluteGaloisGroup K)) :
    AddCommGroup.primaryComponent
      (continuousCohomology 3 (trivialIntegralTopRep ↥U)) p = ⊥ := by
  let e := (ValuationTheory.Completion.separableClosureAutContinuousEquiv K).symm
  let V := U.comap e.toMonoidHom e.continuous
  have hsymm (g : U) : e.symm g.val ∈ V := by
    change e (e.symm g.val) ∈ U
    exact (e.apply_symm_apply g.val).symm ▸ g.property
  let f : ↥V ≃ₜ* ↥U :=
    { toFun := fun g => ⟨e g.val, g.property⟩
      invFun := fun g => ⟨e.symm g.val, hsymm g⟩
      left_inv := fun g => Subtype.ext (e.symm_apply_apply g.val)
      right_inv := fun g => Subtype.ext (e.apply_symm_apply g.val)
      map_mul' := fun g h => Subtype.ext (map_mul e g.val h.val)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  exact trivialIntegralPrimaryH3_eq_bot_of_groupEquiv p f
    (openLocalIntegralPrimaryH3_eq_bot_of_constant_duality K p hp hdual V)

private theorem constantLocalTateTwo_injective (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    Function.Injective (localTatePairingTwoAdjoint K n (T (n : ℕ)) hn) := by
  let A := T (n : ℕ)
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Finite A := inferInstanceAs (Finite (ULift.{u} (ZMod (n : ℕ))))
  have hann (a : A) : (n : ℕ) • a = 0 := by
    apply ULift.ext
    change (n : ℕ) • (show ULift.{u} (ZMod (n : ℕ)) from a).down = 0
    exact ZModModule.char_nsmul_eq_zero (n := (n : ℕ)) _
  exact ((localTatePairingAdjoints_bijective K n A hn continuous_snd hann).2.2).injective

/-- The integral open-subgroup criterion for strict local dimension at an invertible prime. -/
theorem openLocalIntegralPrimaryH3_eq_bot (hp : IsUnit (p : K)) (U : OpenSubgroup G) :
    AddCommGroup.primaryComponent (continuousCohomology 3 (trivialIntegralTopRep ↥U)) p = ⊥ :=
  openLocalIntegralPrimaryH3_eq_bot_of_constant_duality K p hp.ne_zero
    (fun E _ _ _ _ n hn => constantLocalTateTwo_injective E n hn) U

/-- The same strict-dimension criterion on Mathlib's absolute Galois group. -/
theorem openAbsoluteLocalIntegralPrimaryH3_eq_bot_of_isUnit (hp : IsUnit (p : K))
    (U : OpenSubgroup (Field.absoluteGaloisGroup K)) :
    AddCommGroup.primaryComponent (continuousCohomology 3 (trivialIntegralTopRep ↥U)) p = ⊥ :=
  openAbsoluteLocalIntegralPrimaryH3_eq_bot_of_constant_duality K p hp.ne_zero
    (fun E _ _ _ _ n hn => constantLocalTateTwo_injective E n hn) U

/-- In characteristic zero the strict-dimension criterion holds at every prime. -/
theorem openAbsoluteLocalIntegralPrimaryH3_eq_bot [CharZero K]
    (U : OpenSubgroup (Field.absoluteGaloisGroup K)) :
    AddCommGroup.primaryComponent (continuousCohomology 3 (trivialIntegralTopRep ↥U)) p = ⊥ :=
  openAbsoluteLocalIntegralPrimaryH3_eq_bot_of_isUnit K p
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero).isUnit U

end ClassFieldTheory.Brauer
