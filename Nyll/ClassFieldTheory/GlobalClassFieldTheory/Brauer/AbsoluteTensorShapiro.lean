/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.AbsoluteTensorEvaluation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.CompletedTensorBrauerMap

/-! # The absolute tensor cocycle and its completed Shapiro presentation -/

@[expose] public section

open AlgebraicNumberTheory.Valuations CategoryTheory ContinuousCohomology LocalClassFieldTheory
open HilbertRamification
open scoped TensorProduct

noncomputable section
namespace ClassFieldTheory.Brauer

variable {K E F : Type} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
  [FiniteDimensional K E] [IsGalois K E]
  (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) (w : AbsoluteValueExtension v E)

local notation "G" => Gal(E/K)
local notation "D" => absoluteValueDecompositionGroup K (Subtype.val w)
local notation "V" => v.Completion
local notation "M" => LocalizedCompletion v w
local notation "Ω" => SeparableClosure F

attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower
attribute [local instance] scalarTensorUnitsAction

private def restrictThenCompose {P Q R : Type} [Group P] [Group Q] [Group R]
    (f : Q →* P) (g : R →* Q) {A A' : Rep ℤ P} {B : Rep ℤ Q} {C : Rep ℤ R}
    (a : A ⟶ A') (b : Rep.res f A' ⟶ B) (c : Rep.res g B ⟶ C) :
    Rep.res (f.comp g) A ⟶ C :=
  (Rep.resFunctor (f.comp g)).map a ≫ (Rep.resFunctor g).map b ≫ c

private theorem restrictThenCompose_apply {P Q R : Type} [Group P] [Group Q] [Group R]
    (f : Q →* P) (g : R →* Q) {A A' : Rep ℤ P} {B : Rep ℤ Q} {C : Rep ℤ R}
    (a : A ⟶ A') (b : Rep.res f A' ⟶ B) (c : Rep.res g B ⟶ C) (y : A) :
    restrictThenCompose f g a b c y = c (b (a y)) := rfl

private theorem groupCohomologyMap_restrictThenCompose
    {P Q R : Type} [Group P] [Group Q] [Group R]
    (f : Q →* P) (g : R →* Q) {A A' : Rep ℤ P} {B : Rep ℤ Q} {C : Rep ℤ R}
    (a : A ⟶ A') (b : Rep.res f A' ⟶ B) (c : Rep.res g B ⟶ C)
    (x : groupCohomology A 2) :
    groupCohomology.map (f.comp g) (restrictThenCompose f g a b c) 2 x =
      groupCohomology.map g c 2
        (groupCohomology.map f b 2 (groupCohomology.map (MonoidHom.id P) a 2 x)) := by
  let t : Rep.res f A ⟶ B := (Rep.resFunctor f).map a ≫ b
  have ht : (Rep.resFunctor g).map t ≫ c = restrictThenCompose f g a b c := by
    simp only [t, restrictThenCompose]
    rfl
  have h₁ := ConcreteCategory.congr_hom
    (groupCohomology.map_comp (MonoidHom.id P) f a b 2) x
  have h₂ := ConcreteCategory.congr_hom (groupCohomology.map_comp f g t c 2) x
  have h₃ := congrArg (fun m => groupCohomology.map (f.comp g) m 2 x) ht
  exact h₃.symm.trans (h₂.trans (congrArg (groupCohomology.map g c 2) h₁))

private theorem discreteTopRepMap_apply_units
    {P Q : Type} [Group P] [Group Q] [TopologicalSpace P] [TopologicalSpace Q]
    [IsTopologicalGroup P] [IsTopologicalGroup Q]
    {A : Rep ℤ P} {B : Rep ℤ Q} (r : Q →ₜ* P) (f : Rep.res r.toMonoidHom A ⟶ B)
    (x : A) : discreteTopRepMap r f x = f x := rfl

private theorem discreteTopRepH2Equiv_map_symm {P Q : Type}
    [Group P] [Group Q] [TopologicalSpace P] [TopologicalSpace Q]
    [IsTopologicalGroup P] [IsTopologicalGroup Q] [DiscreteTopology P] [DiscreteTopology Q]
    (A : Rep ℤ P) (B : Rep ℤ Q) (r : Q →ₜ* P) (p : Rep.res r.toMonoidHom A ⟶ B)
    (x : groupCohomology A 2) :
    discreteTopRepH2Equiv B (ContinuousCohomology.map r (discreteTopRepMap r p) 2
      ((discreteTopRepH2Equiv A).symm x)) = groupCohomology.map r.toMonoidHom p 2 x := by
  let z := (discreteTopRepH2Equiv A).symm x
  exact (discreteTopRepH2Equiv_map r p z).trans
    (congrArg (groupCohomology.map r.toMonoidHom p 2)
      ((discreteTopRepH2Equiv A).apply_symm_apply x))

private theorem continuousMap_two_eq_comp_of_values {P Q R : Type}
    [Group P] [Group Q] [Group R] [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace R] [IsTopologicalGroup P] [IsTopologicalGroup Q] [IsTopologicalGroup R]
    {A : TopRep.{0} ℤ P} {B : TopRep.{0} ℤ Q} {C : TopRep.{0} ℤ R}
    (r : Q →ₜ* P) (s : R →ₜ* Q) (g : R →ₜ* P)
    (α : TopRep.res r.toMonoidHom A ⟶ B) (β : TopRep.res s.toMonoidHom B ⟶ C)
    (γ : TopRep.res g.toMonoidHom A ⟶ C)
    (hg : ∀ z : R, g z = r (s z)) (hc : ∀ z : A, γ z = β (α z))
    (x : continuousCohomology 2 A) :
    ContinuousCohomology.map g γ 2 x =
      ContinuousCohomology.map s β 2 (ContinuousCohomology.map r α 2 x) := by
  let η : TopRep.res (r.comp s).toMonoidHom A ⟶ C :=
    (TopRep.resFunctor s.toMonoidHom).map α ≫ β
  have h : ContinuousCohomology.map g γ 2 = ContinuousCohomology.map (r.comp s) η 2 :=
    map_eq_of_values 2 γ η hg hc
  have hmul := ContinuousCohomology.map_comp (X := A) (Y := B) (Z := C) r s α β 2
  exact ConcreteCategory.congr_hom (h.trans hmul) x

private theorem continuousMap_two_eq_of_comparison {P Q R : Type}
    [Group P] [Group Q] [Group R] [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace R] [IsTopologicalGroup P] [IsTopologicalGroup Q] [IsTopologicalGroup R]
    {A : TopRep.{0} ℤ P} {B : TopRep.{0} ℤ Q} {C : TopRep.{0} ℤ R}
    (r : Q →ₜ* P) (s : R →ₜ* Q) (g : R →ₜ* P)
    (α : TopRep.res r.toMonoidHom A ⟶ B) (β : TopRep.res s.toMonoidHom B ⟶ C)
    (γ : TopRep.res g.toMonoidHom A ⟶ C)
    (hg : ∀ z : R, g z = r (s z)) (hc : ∀ z : A, γ z = β (α z))
    (x : continuousCohomology 2 A) (y : continuousCohomology 2 B)
    (hy : y = ContinuousCohomology.map r α 2 x) :
    ContinuousCohomology.map s β 2 y = ContinuousCohomology.map g γ 2 x :=
  (congrArg (ContinuousCohomology.map s β 2) hy).trans
    (continuousMap_two_eq_comp_of_values r s g α β γ hg hc x).symm

omit [IsGalois K E] in
private theorem absoluteTensorEvaluation_throughCompletion (e : V ≃ₐ[K] F) :
    let : Algebra V M := localizedCompletionBaseAlgebra v w
    let : Algebra K M := localizedCompletionGlobalAlgebra v w
    let : IsScalarTower K V M := localizedCompletionIsScalarTower v w
    let : Algebra V Ω := ((algebraMap F Ω).comp e.toRingHom).toAlgebra
    let : IsScalarTower K V Ω := IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (algebraMap F Ω) (e.commutes a).symm
    ∀ (b : M →ₐ[V] Ω) (z : F ⊗[K] E),
      absoluteTensorEvaluation ((b.restrictScalars K).comp (localizedCompletionToAlgHom v w)) z =
        b (localTensorEvaluation v hv w
          (Algebra.TensorProduct.map e.symm.toAlgHom (AlgHom.id K E) z)) := by
  intro algebraVM algebraKM towerKVM algebraVΩ towerKVΩ b z
  let j := localizedCompletionToAlgHom v w
  let a := (b.restrictScalars K).comp j
  let f := Algebra.TensorProduct.map e.symm.toAlgHom (AlgHom.id K E)
  let g := localTensorEvaluation v hv w
  change absoluteTensorEvaluation a z = b (g (f z))
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    have hf : f (x ⊗ₜ[K] y) = e.symm x ⊗ₜ[K] y :=
      Algebra.TensorProduct.map_tmul _ _ x y
    have hg : g (e.symm x ⊗ₜ[K] y) = algebraMap V M (e.symm x) * j y :=
      localTensorEvaluation_tmul v hv w (e.symm x) y
    have hb : b (algebraMap V M (e.symm x)) = algebraMap F Ω x :=
      (b.commutes (e.symm x)).trans (congrArg (algebraMap F Ω) (e.apply_symm_apply x))
    calc
      _ = algebraMap F Ω x * b (j y) := absoluteTensorEvaluation_tmul a x y
      _ = b (algebraMap V M (e.symm x)) * b (j y) :=
        congrArg (fun t => t * b (j y)) hb.symm
      _ = b (algebraMap V M (e.symm x) * j y) := (map_mul b _ _).symm
      _ = b (g (e.symm x ⊗ₜ[K] y)) := congrArg (fun t : M => b t) hg.symm
      _ = _ := congrArg (fun t : V ⊗[K] E => b (g t)) hf.symm

private theorem absoluteTensorRestriction_throughCompletion (e : V ≃ₐ[K] F) :
    let : Algebra V M := localizedCompletionBaseAlgebra v w
    let : FiniteDimensional V M := localizedCompletionFiniteDimensional v hv w
    let : IsGalois V M := localizedCompletionIsGalois v w
    let : Algebra K M := localizedCompletionGlobalAlgebra v w
    let : IsScalarTower K V M := localizedCompletionIsScalarTower v w
    let : Algebra V F := e.toRingHom.toAlgebra
    let : Algebra V Ω := ((algebraMap F Ω).comp e.toRingHom).toAlgebra
    let : IsScalarTower V F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower K V Ω := IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (algebraMap F Ω) (e.commutes a).symm
    ∀ (b : M →ₐ[V] Ω) (g : Gal(Ω/F)),
      let j := localizedCompletionToAlgHom v w
      let a := (b.restrictScalars K).comp j
      let d := decompositionGroupEquivAlgebraicLocalizationAut v hv w
      embeddedGaloisRestriction (B := F) a g =
        (d.symm (embeddedGaloisRestriction (B := F) b g)).val := by
  intro algebraVM finVM galVM algebraKM towerKVM algebraVF algebraVΩ towerVFΩ towerKVΩ b g j a d
  let s := embeddedGaloisRestriction (B := F) b
  apply AlgEquiv.ext
  intro x
  apply a.injective
  have ha : a (embeddedGaloisRestriction (B := F) a g x) = g (b (j x)) :=
    embeddedGaloisRestriction_commutes (B := F) a g x
  have hb : b (s g (j x)) = g (b (j x)) := embeddedGaloisRestriction_commutes (B := F) b g (j x)
  have hj := localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    v hv w (d.symm (s g)) x
  change d (d.symm (s g)) (j x) = j ((d.symm (s g)).val x) at hj
  have h : s g (j x) = j ((d.symm (s g)).val x) :=
    (congrArg (fun τ : Gal(M/V) => τ (j x)) (d.apply_symm_apply (s g))).symm.trans hj
  exact ha.trans (hb.symm.trans (congrArg (fun y : M => b y) h))

private theorem absoluteTensorUnitsMap_throughCompletion (e : V ≃ₐ[K] F) :
    let : Algebra V M := localizedCompletionBaseAlgebra v w
    let : FiniteDimensional V M := localizedCompletionFiniteDimensional v hv w
    let : IsGalois V M := localizedCompletionIsGalois v w
    let : Algebra K M := localizedCompletionGlobalAlgebra v w
    let : IsScalarTower K V M := localizedCompletionIsScalarTower v w
    let : MulDistribMulAction D Mˣ := decompositionGroupLocalUnitsAction v hv w
    let : Algebra V F := e.toRingHom.toAlgebra
    let : Algebra V Ω := ((algebraMap F Ω).comp e.toRingHom).toAlgebra
    let : IsScalarTower V F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsScalarTower K V Ω := IsScalarTower.of_algebraMap_eq fun x =>
      congrArg (algebraMap F Ω) (e.commutes x).symm
    let A : Rep ℤ G := Rep.ofMulDistribMulAction G (F ⊗[K] E)ˣ
    let B : Rep ℤ Gal(M/V) := Rep.ofAlgebraAutOnUnits V M
    ∀ (b : M →ₐ[V] Ω) (r : Gal(M/V) →ₜ* G) (p : Rep.res r.toMonoidHom A ⟶ B)
      (_ : ∀ u : A, p u = localTensorEvaluationRepHom v hv w
        ((tensorUnitsRepBaseAlgEquiv (L := E) e.symm).hom u)),
      let a := (b.restrictScalars K).comp (localizedCompletionToAlgHom v w)
      let s := embeddedGaloisRestriction (B := F) b
      let β := galoisUnitsMap s b.toRingHom (embeddedGaloisRestriction_commutes (B := F) b)
      ∀ u : A, absoluteTensorUnitsMap a u = β (discreteTopRepMap r p u) := by
  intro algVM finVM galVM algKM towerKVM act algVF algVΩ towerVFΩ towerKVΩ A B b r p hp a s β u
  let u₀ : Additive (F ⊗[K] E)ˣ := u
  let t := tensorUnitsRepBaseAlgEquiv (L := E) e.symm
  let m := localTensorEvaluationRepHom v hv w
  apply Additive.toMul.injective
  apply Units.ext
  let carrier (x : Additive Ωˣ) : Ω := (x.toMul : Ω)
  have ha := congrArg carrier (absoluteTensorUnitsMap_apply a u)
  have hα := (discreteTopRepMap_apply_units r p u).trans (hp u)
  let uM : Additive Mˣ := m (t.hom u)
  have hβ := congrArg (fun x : B => carrier (β x)) hα
  have hβApply := congrArg carrier
    (galoisUnitsMap_apply s b.toRingHom (embeddedGaloisRestriction_commutes (B := F) b) uM)
  have hm := congrArg (fun x : Additive Mˣ => b (x.toMul : M))
    (localTensorEvaluationRepHom_apply v hv w (t.hom u))
  have hEval := absoluteTensorEvaluation_throughCompletion v hv w e b (u₀.toMul : F ⊗[K] E)
  exact ha.trans (hEval.trans ((hβ.trans (hβApply.trans hm)).symm))

private theorem localTensorRelativeH2Equiv_original_apply :
    let : Algebra V M := localizedCompletionBaseAlgebra v w
    let : FiniteDimensional V M := localizedCompletionFiniteDimensional v hv w
    let : MulDistribMulAction D Mˣ := decompositionGroupLocalUnitsAction v hv w
    ∀ x : groupCohomology (Rep.ofMulDistribMulAction G (V ⊗[K] E)ˣ) 2,
      discreteOriginalH2Equiv (galoisUnitsRep V M) (localTensorRelativeH2Equiv v hv w x) =
        (groupCohomology.mapIso
          (A := Rep.ofAlgebraAutOnUnits V M) (B := Rep.ofMulDistribMulAction D Mˣ)
          (decompositionGroupEquivAlgebraicLocalizationAut v hv w)
          (LinearEquiv.refl ℤ (Additive Mˣ)) (fun _ => rfl) 2).hom
          ((localTensorShapiro v hv w 2).hom x) := by
  intro baseAlgebra finrankVM unitAction x
  exact (discreteOriginalH2Equiv (galoisUnitsRep V M)).apply_symm_apply _

private theorem localTensorRelativeH2Equiv_map_discrete (e : V ≃ₐ[K] F) :
    let : Algebra V M := localizedCompletionBaseAlgebra v w
    let : FiniteDimensional V M := localizedCompletionFiniteDimensional v hv w
    let : MulDistribMulAction D Mˣ := decompositionGroupLocalUnitsAction v hv w
    let A : Rep ℤ G := Rep.ofMulDistribMulAction G (F ⊗[K] E)ˣ
    let T : Rep ℤ D := Rep.ofMulDistribMulAction D Mˣ
    let B : Rep ℤ Gal(M/V) := Rep.ofAlgebraAutOnUnits V M
    let t := tensorUnitsRepBaseAlgEquiv (L := E) e.symm
    let d := decompositionGroupEquivAlgebraicLocalizationAut v hv w
    let dk := (groupCohomology.mapIso (A := B) (B := T)
      d (LinearEquiv.refl ℤ (Additive Mˣ)) (fun _ => rfl) 2).hom
    ∀ (r : Gal(M/V) →ₜ* G) (p : Rep.res r.toMonoidHom A ⟶ B)
      (x : groupCohomology A 2),
      let X := (groupCohomology.functor ℤ G 2).map t.hom x
      groupCohomology.map r.toMonoidHom p 2 x = dk ((localTensorShapiro v hv w 2).hom X) →
      localTensorRelativeH2Equiv v hv w X = ContinuousCohomology.map r
        (discreteTopRepMap r p) 2 ((discreteTopRepH2Equiv A).symm x) := by
  intro algebraVM finrankVM action A T B t d dk r p x X ht
  let z := (discreteTopRepH2Equiv A).symm x
  let zM := ContinuousCohomology.map r (discreteTopRepMap r p) 2 z
  let h₂ := discreteOriginalH2Equiv (galoisUnitsRep V M)
  have hα : discreteTopRepH2Equiv B zM = groupCohomology.map r.toMonoidHom p 2 x :=
    discreteTopRepH2Equiv_map_symm A B r p x
  have hdisc : discreteTopRepH2Equiv B zM = h₂ zM :=
    galoisUnitsDiscreteH2_eq_original (K := V) (E := M) zM
  have hlocal := localTensorRelativeH2Equiv_original_apply v hv w X
  exact h₂.injective (hlocal.trans ((hα.trans ht).symm.trans hdisc))

private theorem tensorH2ToCompletedBrauer_apply_comparison (e : V ≃ₐ[K] F) :
    let : Algebra V M := localizedCompletionBaseAlgebra v w
    let : FiniteDimensional V M := localizedCompletionFiniteDimensional v hv w
    let : IsGalois V M := localizedCompletionIsGalois v w
    let : Algebra V F := e.toRingHom.toAlgebra
    let : Algebra V Ω := ((algebraMap F Ω).comp e.toRingHom).toAlgebra
    let : IsScalarTower V F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let b : M →ₐ[V] Ω := IsSepClosed.lift
    let s := embeddedGaloisRestriction (B := F) b
    let β := galoisUnitsMap s b.toRingHom (embeddedGaloisRestriction_commutes (B := F) b)
    ∀ x : groupCohomology (Rep.ofMulDistribMulAction G (F ⊗[K] E)ˣ) 2,
      tensorH2ToCompletedBrauer v hv w e x =
        ContinuousCohomology.map s β 2 (localTensorRelativeH2Equiv v hv w
          ((groupCohomology.functor ℤ G 2).map
            (tensorUnitsRepBaseAlgEquiv (L := E) e.symm).hom x)) := by
  intro algebraVM finVM galVM algebraVF algebraVΩ towerVFΩ b s β x
  rfl

/-- The chosen completed Shapiro map computes direct evaluation in the
absolute Brauer group, for any embedding of the top normal field. -/
theorem tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map (e : V ≃ₐ[K] F)
    (i : E →ₐ[K] Ω) : tensorH2ToCompletedBrauer v hv w e = absoluteTensorH2Map i := by
  let : Algebra V M := localizedCompletionBaseAlgebra v w
  let : FiniteDimensional V M := localizedCompletionFiniteDimensional v hv w
  let : IsGalois V M := localizedCompletionIsGalois v w
  let : Algebra K M := localizedCompletionGlobalAlgebra v w
  let : IsScalarTower K V M := localizedCompletionIsScalarTower v w
  let : MulDistribMulAction D Mˣ := decompositionGroupLocalUnitsAction v hv w
  let : Algebra V F := e.toRingHom.toAlgebra
  let : Algebra V Ω := ((algebraMap F Ω).comp e.toRingHom).toAlgebra
  let : IsScalarTower V F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower K V Ω := IsScalarTower.of_algebraMap_eq fun a =>
    congrArg (algebraMap F Ω) (e.commutes a).symm
  let j := localizedCompletionToAlgHom v w
  let b : M →ₐ[V] Ω := IsSepClosed.lift
  let a := (b.restrictScalars K).comp j
  rw [absoluteTensorH2Map_eq_of_embeddings i a]
  let A : Rep ℤ G := Rep.ofMulDistribMulAction G (F ⊗[K] E)ˣ
  let T : Rep ℤ D := Rep.ofMulDistribMulAction D Mˣ
  let B : Rep ℤ Gal(M/V) := Rep.ofAlgebraAutOnUnits V M
  let d := decompositionGroupEquivAlgebraicLocalizationAut v hv w
  let t := tensorUnitsRepBaseAlgEquiv (L := E) e.symm
  let m := localTensorEvaluationRepHom v hv w
  let q : Gal(M/V) →* D := d.symm.toMonoidHom
  let k : Rep.res q T ⟶ B :=
    Rep.ofHom ⟨LinearMap.id, fun σ => by
      apply LinearMap.ext
      intro x
      change B.ρ (d (d.symm σ)) x = B.ρ σ x
      rw [d.apply_symm_apply]⟩
  let r : Gal(M/V) →ₜ* G :=
    { toMonoidHom := (D).subtype.comp q
      continuous_toFun := continuous_of_discreteTopology }
  let p : Rep.res r.toMonoidHom A ⟶ B := restrictThenCompose (D).subtype q t.hom m k
  let s := embeddedGaloisRestriction (B := F) b
  let g := embeddedGaloisRestriction (B := F) a
  let ZG : TopRep.{0} ℤ G := TopRep.discreteCoefficientTopRep ℤ G A
  let ZM : TopRep.{0} ℤ Gal(M/V) := galoisUnitsRep V M
  let ZΩ : TopRep.{0} ℤ Gal(Ω/F) := unitsRep F
  let α : TopRep.res r.toMonoidHom ZG ⟶ ZM := discreteTopRepMap r p
  let β : TopRep.res s.toMonoidHom ZM ⟶ ZΩ :=
    galoisUnitsMap s b.toRingHom (embeddedGaloisRestriction_commutes (B := F) b)
  let γ : TopRep.res g.toMonoidHom ZG ⟶ ZΩ := absoluteTensorUnitsMap a
  have hp (u : A) : p u = m (t.hom u) :=
    (restrictThenCompose_apply (D).subtype q t.hom m k u).trans rfl
  have hcoeff (u : ZG) : γ u = β (α u) :=
    absoluteTensorUnitsMap_throughCompletion v hv w e b r p hp u
  have hg (g : Gal(Ω/F)) : embeddedGaloisRestriction a g = r (s g) :=
    absoluteTensorRestriction_throughCompletion v hv w e b g
  apply AddMonoidHom.ext
  intro x
  let z : continuousCohomology 2 ZG := (discreteTopRepH2Equiv A).symm x
  let X := (groupCohomology.functor ℤ G 2).map t.hom x
  let sd := (localTensorShapiro v hv w 2).hom
  let dk := (groupCohomology.mapIso (A := B) (B := T)
    d (LinearEquiv.refl ℤ (Additive Mˣ)) (fun _ => rfl) 2).hom
  have hs : sd X = groupCohomology.map (D).subtype m 2 X :=
    ConcreteCategory.congr_hom (localTensorShapiro_hom_eq_map v hv w 2) X
  have hk (x : groupCohomology T 2) : dk x = groupCohomology.map q k 2 x := rfl
  have ht : groupCohomology.map r.toMonoidHom p 2 x = dk (sd X) := by
    refine (groupCohomologyMap_restrictThenCompose (D).subtype q t.hom m k x).trans ?_
    exact (congrArg (groupCohomology.map q k 2) hs.symm).trans (hk (sd X)).symm
  have hlocal := localTensorRelativeH2Equiv_map_discrete v hv w e r p x ht
  have hleft : tensorH2ToCompletedBrauer v hv w e x =
      ContinuousCohomology.map s β 2 (localTensorRelativeH2Equiv v hv w X) :=
    tensorH2ToCompletedBrauer_apply_comparison v hv w e x
  have hright : absoluteTensorH2Map a x = ContinuousCohomology.map g γ 2 z := rfl
  exact hleft.trans
    ((continuousMap_two_eq_of_comparison r s g α β γ hg hcoeff z
      (localTensorRelativeH2Equiv v hv w X) hlocal).trans hright.symm)

end ClassFieldTheory.Brauer
