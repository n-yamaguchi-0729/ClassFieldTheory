/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairingDevissage
public import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv
public import Nyll.GaloisCohomology.Topology.ContinuousCupLow
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Changing the dualizing exponent in local Tate pairings -/

@[expose] public section

open CategoryTheory ContRepresentation ContinuousCohomology TopRep LocalFieldTheory
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K]

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Mu(" j ")" => separableMuTopRep K (j : ℕ)
local notation "κ" => map (ContinuousMonoidHom.id Γabs)

/-- Compatible Kummer coefficients include the same roots of unity. -/
def separableMuDvdInclusion (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) : Mu(m) ⟶ Mu(n) := by
  let M := separableMuTopRep K (m : ℕ)
  let N := separableMuTopRep K (n : ℕ)
  let : DiscreteTopology M := separableMuTopRep_discrete K m
  let j : M →ₗ[ℤ] N :=
    { toFun := fun a => ⟨a.val, addOrderOf_dvd_iff_nsmul_eq_zero.mp
          ((addOrderOf_dvd_iff_nsmul_eq_zero.mpr a.property).trans h)⟩
      map_add' := fun a b => Subtype.ext rfl
      map_smul' := fun r a => Subtype.ext rfl }
  exact ConcreteCategory.ofHom (C := TopRep.{u} ℤ Γabs) (X := M) (Y := N)
    { toLinearMap := j
      cont := continuous_of_discreteTopology
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro a
        apply Subtype.ext
        rfl }

/-- The change of dualizing target applies the inclusion to the value of
each dual coefficient. -/
def separableMuDualDvdInclusion (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (A : TopRep.{u} ℤ Γabs) : discreteLinearDual A (Mu(m)) ⟶ discreteLinearDual A (Mu(n)) := by
  let M := separableMuTopRep K (m : ℕ)
  let N := separableMuTopRep K (n : ℕ)
  let Dm := discreteLinearDual A M
  let Dn := discreteLinearDual A N
  let j := separableMuDvdInclusion K m n h
  let : Module ℤ A := A.hV2
  let : Module ℤ M := M.hV2
  let : Module ℤ N := N.hV2
  let l : (A →ₗ[ℤ] M) →ₗ[ℤ] (A →ₗ[ℤ] N) :=
    LinearMap.llcomp ℤ A M N j.hom.toContinuousLinearMap.toLinearMap
  exact ConcreteCategory.ofHom (C := TopRep.{u} ℤ Γabs) (X := Dm) (Y := Dn)
    { toLinearMap := l
      cont := continuous_of_discreteTopology
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro f
        apply LinearMap.ext
        intro a
        let f₀ := discreteLinearDualMap A M f
        change j (M.ρ g (f₀ (A.ρ g⁻¹ a))) = N.ρ g (j (f₀ (A.ρ g⁻¹ a)))
        exact j.hom.isIntertwining g _ }

/-- Changing the target of a dual has the expected effect on the actual
evaluation pairing. -/
theorem separableMuDualDvdInclusion_evaluation (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (A : TopRep.{u} ℤ Γabs) (a : A) (l : discreteLinearDual A (Mu(m))) :
    discreteLinearDualIntEvaluation A (Mu(n)) a (separableMuDualDvdInclusion K m n h A l) =
      separableMuDvdInclusion K m n h (discreteLinearDualIntEvaluation A (Mu(m)) a l) := rfl

/-- For coefficients killed by the smaller exponent, the natural inclusion
of duals is a bijection on the same Galois representations. -/
theorem separableMuDualDvdInclusion_bijective (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (A : TopRep.{u} ℤ Γabs) (hA : ∀ a : A, (m : ℕ) • a = 0) :
    Function.Bijective (separableMuDualDvdInclusion K m n h A) := by
  let M := separableMuTopRep K (m : ℕ)
  let N := separableMuTopRep K (n : ℕ)
  let Dm := discreteLinearDual A M
  let Dn := discreteLinearDual A N
  let : Module ℤ A := A.hV2
  let : Module ℤ M := M.hV2
  let : Module ℤ N := N.hV2
  constructor
  · intro f g hfg
    change discreteLinearDualMap A M f = discreteLinearDualMap A M g
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun l : Dn => (discreteLinearDualMap A N l a).val) hfg
  · intro f
    let l := discreteLinearDualMap A N f
    have hl (a : A) : (m : ℕ) • l a = 0 := by
      rw [← map_nsmul, hA, map_zero]
    let l₀ : A →ₗ[ℤ] M :=
      { toFun := fun a => ⟨(l a).val, congrArg (fun x : N => x.val) (hl a)⟩
        map_add' := fun a b => Subtype.ext (congrArg (fun x : N => x.val) (l.map_add a b))
        map_smul' := fun r a => Subtype.ext (congrArg (fun x : N => x.val) (l.map_smul r a)) }
    let f₀ : Dm := l₀
    refine ⟨f₀, ?_⟩
    change discreteLinearDualMap A N (separableMuDualDvdInclusion K m n h A f₀) = l
    exact LinearMap.ext fun a => Subtype.ext rfl

/-- Dual groups and their continuous cohomology use the same smaller-target
inclusion when the original coefficient is annihilated by the smaller exponent. -/
def separableMuDualDvdCohomologyEquiv (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (A : TopRep.{u} ℤ Γabs) (hA : ∀ a : A, (m : ℕ) • a = 0) (i : ℕ) :
    let Dm : TopRep.{u} ℤ Γabs := discreteLinearDual A (Mu(m))
    let Dn : TopRep.{u} ℤ Γabs := discreteLinearDual A (Mu(n))
    continuousCohomology (k := ℤ) (G := Γabs) i Dm ≃+
      continuousCohomology (k := ℤ) (G := Γabs) i Dn := by
  intro Dm Dn
  let f : Dm ⟶ Dn := separableMuDualDvdInclusion K m n h A
  let e := discreteCoefficientIsoOfBijective f (separableMuDualDvdInclusion_bijective K m n h A hA)
  let k := map (X := Dm) (Y := Dn) (ContinuousMonoidHom.id Γabs) f i
  exact AddEquiv.ofBijective k.hom.toLinearMap.toAddMonoidHom
    (map_bijective_of_coeffIso e i)

theorem separableMuDualDvdCohomologyEquiv_apply (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (A : TopRep.{u} ℤ Γabs) (hA : ∀ a : A, (m : ℕ) • a = 0) (i : ℕ)
    (x : continuousCohomology i (discreteLinearDual A (Mu(m)))) :
    separableMuDualDvdCohomologyEquiv K m n h A hA i x =
      κ (separableMuDualDvdInclusion K m n h A) i x := rfl

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The trace target changes by including torsion into the same Brauer group. -/
def localKummerTraceDvdInclusion (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) :
    ZMod (m : ℕ) →+ ZMod (n : ℕ) :=
  let j : brTorsion K m →+ brTorsion K n :=
    { toFun := fun a => ⟨a.val, addOrderOf_dvd_iff_nsmul_eq_zero.mp
          ((addOrderOf_dvd_iff_nsmul_eq_zero.mpr a.property).trans h)⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  (zmodEquivLocalBrauerTorsion K n).symm.toAddMonoidHom.comp
    (j.comp (zmodEquivLocalBrauerTorsion K m).toAddMonoidHom)

theorem localKummerTraceDvdInclusion_rat (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) (a : ZMod (m : ℕ)) :
    zmodToRationalCircle n n.pos (localKummerTraceDvdInclusion K m n h a) =
      zmodToRationalCircle m m.pos a := by
  rw [← localBrauerInvariant_zmodEquivLocalBrauerTorsion K n,
    ← localBrauerInvariant_zmodEquivLocalBrauerTorsion K m]
  let e := zmodEquivLocalBrauerTorsion K n
  let x : brTorsion K n := ⟨(zmodEquivLocalBrauerTorsion K m a).val,
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      ((addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        (zmodEquivLocalBrauerTorsion K m a).property).trans h)⟩
  change localBrauerInvariant K (e (e.symm x)).val =
    localBrauerInvariant K (zmodEquivLocalBrauerTorsion K m a).val
  rw [e.apply_symm_apply]

/-- The scalar target inclusion is injective and identifies exactly the
smaller-exponent torsion inside the larger trace target. -/
theorem mem_range_localKummerTraceDvdInclusion_iff (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (a : ZMod (n : ℕ)) : a ∈ (localKummerTraceDvdInclusion K m n h).range ↔ (m : ℕ) • a = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [← map_nsmul]
    have hb : (m : ℕ) • b = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (m : ℕ)), ZMod.natCast_self, zero_smul]
    rw [hb, map_zero]
  · intro ha
    have hzero : (m : ℕ) • zmodToRationalCircle n n.pos a = 0 := by
      rw [← map_nsmul, ha, map_zero]
    obtain ⟨b, hb⟩ := (mem_range_zmodToRationalCircle_iff m m.pos _).mpr hzero
    exact ⟨b, zmodToRationalCircle_injective n n.pos
      ((localKummerTraceDvdInclusion_rat K m n h b).trans hb)⟩

theorem localKummerTraceDvdInclusion_injective (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) :
    Function.Injective (localKummerTraceDvdInclusion K m n h) := by
  intro a b hab
  apply zmodToRationalCircle_injective m m.pos
  rw [← localKummerTraceDvdInclusion_rat K m n h a,
    ← localKummerTraceDvdInclusion_rat K m n h b, hab]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem separableMuDvdInclusion_H2ToBr (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (x : continuousCohomology 2 (Mu(m))) :
    separableMuH2ToBr K n (κ (separableMuDvdInclusion K m n h) 2 x) = separableMuH2ToBr K m x := by
  let j := separableMuDvdInclusion K m n h
  let idG := ContinuousMonoidHom.id Γabs
  obtain ⟨z, rfl⟩ := π_surjective (Mu(m)) 2 x
  have hp := ConcreteCategory.congr_hom (π_map idG j 2) z
  change κ j 2 (π (Mu(m)) 2 z) = π (Mu(n)) 2 (cocyclesMap idG j 2 z) at hp
  rw [hp, separableMuH2ToBr_π, separableMuH2ToBr_π]
  have hj : (TopRep.resFunctor (idG : Γabs →* Γabs)).map j ≫ separableMuInclusion K n =
      separableMuInclusion K m := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro a
    rfl
  have hc := cocyclesMap_comp (X := Mu(m)) (Y := Mu(n)) (Z := unitsRep K)
    idG idG j (separableMuInclusion K n) 2
  change cocyclesMap idG
    ((TopRep.resFunctor (idG : Γabs →* Γabs)).map j ≫ separableMuInclusion K n) 2 = _ at hc
  rw [hj] at hc
  exact congrArg (π (unitsRep K) 2) (ConcreteCategory.congr_hom hc z).symm

/-- The two local Kummer traces are related by the inclusion of their
actual arithmetic Brauer invariants. -/
theorem localKummerTrace_dvd (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (hm : ((m : ℕ) : K) ≠ 0) (hn : ((n : ℕ) : K) ≠ 0) (x : continuousCohomology 2 (Mu(m))) :
    localKummerTrace K n hn (κ (separableMuDvdInclusion K m n h) 2 x) =
      localKummerTraceDvdInclusion K m n h (localKummerTrace K m hm x) := by
  apply zmodToRationalCircle_injective n n.pos
  rw [zmodToRationalCircle_localKummerTrace, localKummerTraceDvdInclusion_rat,
    zmodToRationalCircle_localKummerTrace, separableMuDvdInclusion_H2ToBr]

section Pairings

variable (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
  (hm : ((m : ℕ) : K) ≠ 0) (hn : ((n : ℕ) : K) ≠ 0)
  (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [DiscreteTopology A]

/-- The degree-one pairing uses the same class after inclusion of roots
in the dual and inclusion of arithmetic trace targets. -/
theorem localTatePairingOne_dvd (x : continuousCohomology 1 A)
    (y : continuousCohomology 1 (discreteLinearDual A (separableMuTopRep K m))) :
    localTatePairingOne K n A hn x (κ (separableMuDualDvdInclusion K m n h A) 1 y) =
      localKummerTraceDvdInclusion K m n h (localTatePairingOne K m A hm x y) := by
  let M := separableMuTopRep K (m : ℕ)
  let N := separableMuTopRep K (n : ℕ)
  let Dm := discreteLinearDual A M
  let Dn := discreteLinearDual A N
  let r := ContinuousMonoidHom.id Γabs
  let f : Dm ⟶ Dn := separableMuDualDvdInclusion K m n h A
  let j : M ⟶ N := separableMuDvdInclusion K m n h
  have hc := map_cupOneOne
    (A := A) (B := Dm) (C := M) (A' := A) (B' := Dn) (C' := N)
    (discreteLinearDualIntEvaluation A M) (discreteLinearDualIntEvaluation_continuous A M)
    (discreteLinearDualIntEvaluation_equivariant A M) r (𝟙 A) f j
    (discreteLinearDualIntEvaluation A N) (discreteLinearDualIntEvaluation_continuous A N)
    (discreteLinearDualIntEvaluation_equivariant A N)
    (fun a b => (separableMuDualDvdInclusion_evaluation K m n h A a b).symm) x y
  simp only [r, ContinuousCohomology.map_id, ConcreteCategory.id_apply] at hc
  exact (congrArg (localKummerTrace K n hn) hc.symm).trans
    (localKummerTrace_dvd K m n h hm hn _)

/-- The invariant-left pairing respects changing the actual dualizing exponent. -/
theorem localTatePairingZero_dvd (x : continuousCohomology 0 A)
    (y : continuousCohomology 2 (discreteLinearDual A (separableMuTopRep K m))) :
    localTatePairingZero K n A hn x (κ (separableMuDualDvdInclusion K m n h A) 2 y) =
      localKummerTraceDvdInclusion K m n h (localTatePairingZero K m A hm x y) := by
  let M := separableMuTopRep K (m : ℕ)
  let N := separableMuTopRep K (n : ℕ)
  let Dm := discreteLinearDual A M
  let Dn := discreteLinearDual A N
  let r := ContinuousMonoidHom.id Γabs
  let f : Dm ⟶ Dn := separableMuDualDvdInclusion K m n h A
  let j : M ⟶ N := separableMuDvdInclusion K m n h
  have hc := map_cupZeroTwo
    (A := A) (B := Dm) (C := M) (A' := A) (B' := Dn) (C' := N)
    (discreteLinearDualIntEvaluation A M) (discreteLinearDualIntEvaluation_continuous A M)
    (discreteLinearDualIntEvaluation_equivariant A M) r (𝟙 A) f j
    (discreteLinearDualIntEvaluation A N) (discreteLinearDualIntEvaluation_continuous A N)
    (discreteLinearDualIntEvaluation_equivariant A N)
    (fun a b => (separableMuDualDvdInclusion_evaluation K m n h A a b).symm) x y
  simp only [r, ContinuousCohomology.map_id, ConcreteCategory.id_apply] at hc
  exact (congrArg (localKummerTrace K n hn) hc.symm).trans
    (localKummerTrace_dvd K m n h hm hn _)

/-- The invariant-right pairing respects changing the actual dualizing exponent. -/
theorem localTatePairingTwo_dvd (x : continuousCohomology 2 A)
    (y : continuousCohomology 0 (discreteLinearDual A (separableMuTopRep K m))) :
    localTatePairingTwo K n A hn x (κ (separableMuDualDvdInclusion K m n h A) 0 y) =
      localKummerTraceDvdInclusion K m n h (localTatePairingTwo K m A hm x y) := by
  let M := separableMuTopRep K (m : ℕ)
  let N := separableMuTopRep K (n : ℕ)
  let Dm := discreteLinearDual A M
  let Dn := discreteLinearDual A N
  let r := ContinuousMonoidHom.id Γabs
  let f : Dm ⟶ Dn := separableMuDualDvdInclusion K m n h A
  let j : M ⟶ N := separableMuDvdInclusion K m n h
  have hc := map_cupTwoZero
    (A := A) (B := Dm) (C := M) (A' := A) (B' := Dn) (C' := N)
    (discreteLinearDualIntEvaluation A M) (discreteLinearDualIntEvaluation_continuous A M)
    (discreteLinearDualIntEvaluation_equivariant A M) r (𝟙 A) f j
    (discreteLinearDualIntEvaluation A N) (discreteLinearDualIntEvaluation_continuous A N)
    (discreteLinearDualIntEvaluation_equivariant A N)
    (fun a b => (separableMuDualDvdInclusion_evaluation K m n h A a b).symm) x y
  simp only [r, ContinuousCohomology.map_id, ConcreteCategory.id_apply] at hc
  exact (congrArg (localKummerTrace K n hn) hc.symm).trans
    (localKummerTrace_dvd K m n h hm hn _)

end Pairings

private theorem traceCharacter_targetChange_bijective (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    {A B : Type u} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (hm : ∀ a : A, (m : ℕ) • a = 0) :
    Function.Bijective (fun φ : A →+ ZMod (m : ℕ) =>
      (localKummerTraceDvdInclusion K m n h).comp (φ.comp e.symm.toAddMonoidHom)) := by
  let i := localKummerTraceDvdInclusion K m n h
  have hi := localKummerTraceDvdInclusion_injective K m n h
  constructor
  · intro φ ψ hφψ
    ext a
    apply hi
    have h := DFunLike.congr_fun hφψ (e a)
    change i (φ (e.symm (e a))) = i (ψ (e.symm (e a))) at h
    rwa [e.symm_apply_apply] at h
  · intro ψ
    let l := ψ.comp e.toAddMonoidHom
    have hmem (a : A) : l a ∈ i.range := by
      apply (mem_range_localKummerTraceDvdInclusion_iff K m n h _).mpr
      rw [← map_nsmul, hm, map_zero]
    choose f hf using hmem
    let φ : A →+ ZMod (m : ℕ) :=
      { toFun := f
        map_zero' := hi ((hf 0).trans ((map_zero l).trans (map_zero i).symm))
        map_add' := fun a b => hi <|
          (hf (a + b)).trans ((map_add l a b).trans
            (((map_add i (f a) (f b)).trans (congrArg₂ (· + ·) (hf a) (hf b))).symm)) }
    refine ⟨φ, AddMonoidHom.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective b
    change i (f (e.symm (e a))) = ψ (e a)
    rw [e.symm_apply_apply]
    exact hf a

private theorem adjoint_bijective_of_dvd (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    {X A B : Type u} [AddCommGroup X] [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (hm : ∀ a : A, (m : ℕ) • a = 0)
    (φ : X →+ (A →+ ZMod (m : ℕ))) (ψ : X →+ (B →+ ZMod (n : ℕ)))
    (hp : ∀ x a, ψ x (e a) = localKummerTraceDvdInclusion K m n h (φ x a))
    (hφ : Function.Bijective φ) : Function.Bijective ψ := by
  let q := fun f : A →+ ZMod (m : ℕ) =>
    (localKummerTraceDvdInclusion K m n h).comp (f.comp e.symm.toAddMonoidHom)
  have hq (x : X) : ψ x = q (φ x) := by
    ext b
    obtain ⟨a, rfl⟩ := e.surjective b
    change ψ x (e a) = localKummerTraceDvdInclusion K m n h (φ x (e.symm (e a)))
    rw [e.symm_apply_apply, hp]
  change Function.Bijective (fun x => ψ x)
  simp only [hq]
  exact (traceCharacter_targetChange_bijective K m n h e hm).comp hφ

private theorem localTatePairingZeroAdjoint_bijective_of_dvd
    (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) (hm : ((m : ℕ) : K) ≠ 0) (hn : ((n : ℕ) : K) ≠ 0)
    (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A] (hA : ∀ a : A, (m : ℕ) • a = 0)
    (hp : Function.Bijective (localTatePairingZeroAdjoint K m A hm)) :
    Function.Bijective (localTatePairingZeroAdjoint K n A hn) := by
  let D := discreteLinearDual A (Mu(m))
  let D' := discreteLinearDual A (Mu(n))
  let X := continuousCohomology 0 A
  let Y := continuousCohomology 2 D
  let Y' := continuousCohomology 2 D'
  let f : X →+ (Y →+ ZMod (m : ℕ)) := localTatePairingZeroAdjoint K m A hm
  let g : X →+ (Y' →+ ZMod (n : ℕ)) := localTatePairingZeroAdjoint K n A hn
  let e : Y ≃+ Y' := separableMuDualDvdCohomologyEquiv K m n h A hA 2
  have hf : Function.Bijective f := hp
  have hCompat (x : X) (y : Y) :
      g x (e y) = localKummerTraceDvdInclusion K m n h (f x y) := by
    change localTatePairingZero K n A hn x (e y) =
      localKummerTraceDvdInclusion K m n h (localTatePairingZero K m A hm x y)
    have he := separableMuDualDvdCohomologyEquiv_apply K m n h A hA 2 y
    exact (congrArg (localTatePairingZero K n A hn x) he).trans
      (localTatePairingZero_dvd K m n h hm hn A x y)
  have hz : ∀ y : Y, (m : ℕ) • y = 0 := nsmul_continuousCohomology_eq_zero_of_coefficients D m
    (separableMu_dual_nsmul_eq_zero K m A) 2
  change Function.Bijective g
  clear_value f g e
  exact adjoint_bijective_of_dvd K m n h e hz f g hCompat hf


private theorem localTatePairingOneAdjoint_bijective_of_dvd
    (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) (hm : ((m : ℕ) : K) ≠ 0) (hn : ((n : ℕ) : K) ≠ 0)
    (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A] (hA : ∀ a : A, (m : ℕ) • a = 0)
    (hp : Function.Bijective (localTatePairingOneAdjoint K m A hm)) :
    Function.Bijective (localTatePairingOneAdjoint K n A hn) := by
  let D := discreteLinearDual A (Mu(m))
  let D' := discreteLinearDual A (Mu(n))
  let X := continuousCohomology 1 A
  let Y := continuousCohomology 1 D
  let Y' := continuousCohomology 1 D'
  let f : X →+ (Y →+ ZMod (m : ℕ)) := localTatePairingOneAdjoint K m A hm
  let g : X →+ (Y' →+ ZMod (n : ℕ)) := localTatePairingOneAdjoint K n A hn
  let e : Y ≃+ Y' := separableMuDualDvdCohomologyEquiv K m n h A hA 1
  have hf : Function.Bijective f := hp
  have hCompat (x : X) (y : Y) :
      g x (e y) = localKummerTraceDvdInclusion K m n h (f x y) := by
    change localTatePairingOne K n A hn x (e y) =
      localKummerTraceDvdInclusion K m n h (localTatePairingOne K m A hm x y)
    have he := separableMuDualDvdCohomologyEquiv_apply K m n h A hA 1 y
    exact (congrArg (localTatePairingOne K n A hn x) he).trans
      (localTatePairingOne_dvd K m n h hm hn A x y)
  have hz : ∀ y : Y, (m : ℕ) • y = 0 := nsmul_continuousCohomology_eq_zero_of_coefficients D m
    (separableMu_dual_nsmul_eq_zero K m A) 1
  change Function.Bijective g
  clear_value f g e
  exact adjoint_bijective_of_dvd K m n h e hz f g hCompat hf


private theorem localTatePairingTwoAdjoint_bijective_of_dvd
    (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) (hm : ((m : ℕ) : K) ≠ 0) (hn : ((n : ℕ) : K) ≠ 0)
    (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A] (hA : ∀ a : A, (m : ℕ) • a = 0)
    (hp : Function.Bijective (localTatePairingTwoAdjoint K m A hm)) :
    Function.Bijective (localTatePairingTwoAdjoint K n A hn) := by
  let D := discreteLinearDual A (Mu(m))
  let D' := discreteLinearDual A (Mu(n))
  let X := continuousCohomology 2 A
  let Y := continuousCohomology 0 D
  let Y' := continuousCohomology 0 D'
  let f : X →+ (Y →+ ZMod (m : ℕ)) := localTatePairingTwoAdjoint K m A hm
  let g : X →+ (Y' →+ ZMod (n : ℕ)) := localTatePairingTwoAdjoint K n A hn
  let e : Y ≃+ Y' := separableMuDualDvdCohomologyEquiv K m n h A hA 0
  have hf : Function.Bijective f := hp
  have hCompat (x : X) (y : Y) :
      g x (e y) = localKummerTraceDvdInclusion K m n h (f x y) := by
    change localTatePairingTwo K n A hn x (e y) =
      localKummerTraceDvdInclusion K m n h (localTatePairingTwo K m A hm x y)
    have he := separableMuDualDvdCohomologyEquiv_apply K m n h A hA 0 y
    exact (congrArg (localTatePairingTwo K n A hn x) he).trans
      (localTatePairingTwo_dvd K m n h hm hn A x y)
  have hz : ∀ y : Y, (m : ℕ) • y = 0 := nsmul_continuousCohomology_eq_zero_of_coefficients D m
    (separableMu_dual_nsmul_eq_zero K m A) 0
  change Function.Bijective g
  clear_value f g e
  exact adjoint_bijective_of_dvd K m n h e hz f g hCompat hf


/-- The three actual perfect pairings for the smaller exponent imply the
same perfect pairings for every multiple of it that remains étale. -/
theorem localTatePairingAdjoints_bijective_of_dvd
    (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) (hm : ((m : ℕ) : K) ≠ 0) (hn : ((n : ℕ) : K) ≠ 0)
    (A : TopRep.{u} ℤ Γabs) [DiscreteTopology A] (hA : ∀ a : A, (m : ℕ) • a = 0)
    (hp : Function.Bijective (localTatePairingZeroAdjoint K m A hm) ∧
      Function.Bijective (localTatePairingOneAdjoint K m A hm) ∧
      Function.Bijective (localTatePairingTwoAdjoint K m A hm)) :
    Function.Bijective (localTatePairingZeroAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n A hn) := by
  exact ⟨localTatePairingZeroAdjoint_bijective_of_dvd K m n h hm hn A hA hp.1,
    localTatePairingOneAdjoint_bijective_of_dvd K m n h hm hn A hA hp.2.1,
    localTatePairingTwoAdjoint_bijective_of_dvd K m n h hm hn A hA hp.2.2⟩

end ClassFieldTheory.Brauer
