/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Kummer
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology
public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Mathlib.FieldTheory.Galois.Profinite

/-! # Conjugation of the original continuous Kummer classes -/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousCohomology ContRepresentation TopRep KummerTheory
open scoped Topology

namespace ClassFieldTheory.Brauer

universe u

variable (L : Type u) [Field L]

local notation "Ω" => SeparableClosure L
local notation "G" => Gal(Ω/L)
local notation "U" => unitsRep L

/-- Apply the semilinear field automorphism to the original separable-closure units. -/
def separableKummerConjugateUnits (e : Ω ≃+* Ω) : U →+ U := by
  change Additive (Ωˣ) →+ Additive (Ωˣ)
  exact (Units.map e.toMonoidHom).toAdditive

private theorem separableKummerConjugateUnits_base (baseAut : L ≃+* L)
    (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x)) (a : Lˣ) :
    separableKummerConjugateUnits L lift (baseUnitValue L a) =
      baseUnitValue L (Units.map baseAut.toMonoidHom a) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact hlift (a : L)

/-- The actual inverse conjugation used to pull back the Galois arguments. -/
def separableKummerConjugationPullback (baseAut : L ≃+* L) (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x)) : G →ₜ* G :=
  let j := (semilinearGaloisConjugateContinuousEquiv baseAut lift hlift).symm
  ⟨j.toMulEquiv.toMonoidHom, j.continuous_toFun⟩

private theorem separableKummerConjugateUnits_action (baseAut : L ≃+* L)
    (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x)) (σ : G) (x : U) :
    separableKummerConjugateUnits L lift
        ((U).ρ (separableKummerConjugationPullback L baseAut lift hlift σ) x) =
      (U).ρ σ (separableKummerConjugateUnits L lift x) := by
  apply Additive.toMul.injective
  apply Units.ext
  let j := semilinearGaloisConjugateContinuousEquiv baseAut lift hlift
  let a : Ωˣ := (show Additive (Ωˣ) from x).toMul
  have h := congrArg (fun γ : G => γ (lift (a : Ω))) (j.apply_symm_apply σ)
  change j (j.symm σ) (lift (a : Ω)) = σ (lift (a : Ω)) at h
  rw [show j (j.symm σ) = semilinearGaloisConjugate baseAut lift hlift (j.symm σ) from rfl,
    semilinearGaloisConjugate_apply, lift.symm_apply_apply] at h
  exact h

/-- Apply the same field automorphism to the actual roots-of-unity subgroup. -/
def separableKummerConjugateRoots (e : Ω ≃+* Ω) (n : ℕ+) :
    separableMuTopRep L n →+ separableMuTopRep L n := by
  change unitsTorsionSubmodule L n →+ unitsTorsionSubmodule L n
  refine
    { toFun := fun x => ⟨separableKummerConjugateUnits L e x.val, ?_⟩
      map_zero' := ?_
      map_add' := ?_ }
  · have hx : (n : ℕ) • x.val = 0 := x.property
    change (n : ℕ) • separableKummerConjugateUnits L e x.val = 0
    rw [← map_nsmul, hx, map_zero]
  · exact Subtype.ext (map_zero (separableKummerConjugateUnits L e))
  · intro x y
    exact Subtype.ext (map_add (separableKummerConjugateUnits L e) x.val y.val)

/-- The coefficient map applies the original field automorphism to each actual root. -/
def separableKummerConjugationCoefficient (baseAut : L ≃+* L) (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x)) (n : ℕ+) :
    TopRep.res (separableKummerConjugationPullback L baseAut lift hlift).toMonoidHom
      (separableMuTopRep L n) ⟶ separableMuTopRep L n := by
  let Y := separableMuTopRep L n
  let r := separableKummerConjugationPullback L baseAut lift hlift
  let X : TopRep.{u} ℤ G := TopRep.res r.toMonoidHom Y
  change X ⟶ Y
  let : DiscreteTopology X := by
    change DiscreteTopology Y
    exact separableMuTopRep_discrete L n
  let f : X →L[ℤ] Y :=
    ⟨(separableKummerConjugateRoots L lift n).toIntLinearMap, continuous_of_discreteTopology⟩
  let F : X.ρ →ⁱL Y.ρ :=
    { toContinuousLinearMap := f
      isIntertwining' := by
        intro σ
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        exact separableKummerConjugateUnits_action L baseAut lift hlift σ x.val }
  exact ConcreteCategory.ofHom (C := TopRep.{u} ℤ G) F

/-- A conjugated Kummer root has power equal to the conjugated original unit. -/
theorem separableKummerConjugateRoot_power (baseAut : L ≃+* L) (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x))
    (n : ℕ+) (a : Lˣ) (β : U)
    (hβ : (n : ℕ) • β = baseUnitValue L a) :
    (n : ℕ) • separableKummerConjugateUnits L lift β =
      baseUnitValue L (Units.map baseAut.toMonoidHom a) := by
  rw [← map_nsmul, hβ]
  exact separableKummerConjugateUnits_base L baseAut lift hlift a

/-- Transporting a specified Kummer root transports its actual crossed homomorphism. -/
theorem rootKummerCrossedHom_conjugation (baseAut : L ≃+* L) (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x))
    (n : ℕ+) (a : Lˣ) (β : U)
    (hβ : (n : ℕ) • β = baseUnitValue L a) (σ : G) :
    separableKummerConjugationCoefficient L baseAut lift hlift n
      ((rootKummerCrossedHom L n a β hβ).toFun
        (separableKummerConjugationPullback L baseAut lift hlift σ)) =
      (rootKummerCrossedHom L n (Units.map baseAut.toMonoidHom a)
        (separableKummerConjugateUnits L lift β)
        (separableKummerConjugateRoot_power L baseAut lift hlift n a β hβ)).toFun σ := by
  apply Subtype.ext
  change separableKummerConjugateUnits L lift
      ((U).ρ (separableKummerConjugationPullback L baseAut lift hlift σ) β - β) =
    (U).ρ σ (separableKummerConjugateUnits L lift β) - separableKummerConjugateUnits L lift β
  rw [map_sub, separableKummerConjugateUnits_action L baseAut lift hlift]

private theorem map_crossedHom_cocycle_eq_of_values
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [LocallyCompactSpace Γ]
    {X Y : TopRep.{u} ℤ Γ} (r : Γ →ₜ* Γ)
    (f : TopRep.res r.toMonoidHom X ⟶ Y)
    (c : CrossedHom X) (c' : CrossedHom Y)
    (h : ∀ g, f (c.toFun (r g)) = c'.toFun g) :
    cocyclesMap r f 1 c.toCocycle = c'.toCocycle := by
  let C := homogeneousCochains Y
  let D := homogeneousCochains X
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  have hi := (ModuleCat.mono_iff_injective (F.map (C.iCycles 1))).mp inferInstance
  apply hi
  change C.iCycles 1 (cocyclesMap r f 1 c.toCocycle) = C.iCycles 1 c'.toCocycle
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  apply ContinuousMap.ext
  intro g'
  have hf : (C.iCycles 1 (cocyclesMap r f 1 c.toCocycle)).val g g' =
      f ((D.iCycles 1 c.toCocycle).val (r g) (r g')) := by
    change resolutionTupleHomeomorph Γ Y 2
      (C.iCycles 1 (cocyclesMap r f 1 c.toCocycle)).val ![g, g'] = _
    rw [cochainOfMappedCocycle]
    exact resolutionTupleHomeomorph_cochainsMap Γ X Y r f 1 (D.iCycles 1 c.toCocycle) ![g, g']
  rw [hf, c.iCycles_toCocycle, c'.iCycles_toCocycle]
  change f (c.toFun (r g') - c.toFun (r g)) = c'.toFun g' - c'.toFun g
  rw [map_sub, h g', h g]

/-- The original cohomology map for conjugation sends the Kummer class of a unit to that
of its conjugate. Both classes are evaluated on the conjugate of the same chosen root. -/
theorem separableKummerH1Class_conjugation (baseAut : L ≃+* L) (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x))
    (n : ℕ+) (hn : ((n : ℕ) : L) ≠ 0) (a : Lˣ) :
    ContinuousCohomology.map (separableKummerConjugationPullback L baseAut lift hlift)
      (separableKummerConjugationCoefficient L baseAut lift hlift n) 1
      (separableKummerH1Class L n hn a) =
        separableKummerH1Class L n hn (Units.map baseAut.toMonoidHom a) := by
  let κ := separableKummerConjugationPullback L baseAut lift hlift
  let φ := separableKummerConjugationCoefficient L baseAut lift hlift n
  let M := separableMuTopRep L n
  change ContinuousCohomology.map κ φ 1 (separableKummerH1Class L n hn a) =
    separableKummerH1Class L n hn (Units.map baseAut.toMonoidHom a)
  obtain ⟨β, hβ⟩ := separableUnits_nsmul_surjective L n hn (baseUnitValue L a)
  let c := rootKummerCrossedHom L n a β hβ
  let c' := rootKummerCrossedHom L n (Units.map baseAut.toMonoidHom a)
    (separableKummerConjugateUnits L lift β)
    (separableKummerConjugateRoot_power L baseAut lift hlift n a β hβ)
  let : LocallyCompactSpace G := by
    let hCompact : CompactSpace G :=
      (InfiniteGalois.continuousMulEquivToLimit L Ω).symm.compactSpace
    let : T2Space G := krullTopology_t2
    exact LocallyCompactSpace.of_hasBasis
      (fun g => hCompact.isCompact_univ.isCompact_isClosed_basis_nhds (x := g) Filter.univ_mem)
      (fun _ _ h => h.2.1)
  have h : cocyclesMap κ φ 1 c.toCocycle = c'.toCocycle :=
    map_crossedHom_cocycle_eq_of_values κ φ c c'
      (rootKummerCrossedHom_conjugation L baseAut lift hlift n a β hβ)
  have hsource : separableKummerH1Class L n hn a = π M 1 c.toCocycle :=
    separableKummerH1Class_eq_root L n hn a β hβ
  have htarget : separableKummerH1Class L n hn (Units.map baseAut.toMonoidHom a) =
      π M 1 c'.toCocycle :=
    separableKummerH1Class_eq_root L n hn (Units.map baseAut.toMonoidHom a)
      (separableKummerConjugateUnits L lift β)
      (separableKummerConjugateRoot_power L baseAut lift hlift n a β hβ)
  calc
    _ = ContinuousCohomology.map κ φ 1 (π M 1 c.toCocycle) :=
      congrArg (ContinuousCohomology.map κ φ 1) hsource
    _ = π M 1 (cocyclesMap κ φ 1 c.toCocycle) :=
      ConcreteCategory.congr_hom (π_map κ φ 1) c.toCocycle
    _ = π M 1 c'.toCocycle := congrArg (π M 1) h
    _ = _ := htarget.symm

/-- The original field automorphism acts on the original unit power quotient. -/
def separableKummerPowerClassConjugation (τ : L ≃+* L) (n : ℕ+) :
    Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range →*
      Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range := by
  let P := (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range
  refine QuotientGroup.map P P (Units.map τ.toMonoidHom) ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨Units.map τ.toMonoidHom a, (map_pow (Units.map τ.toMonoidHom) a (n : ℕ)).symm⟩

/-- The actual Kummer isomorphism intertwines conjugation on every power class. -/
theorem separableMuH1EquivPowerClasses_conjugation (baseAut : L ≃+* L) (lift : Ω ≃+* Ω)
    (hlift : ∀ x : L, lift (algebraMap L Ω x) = algebraMap L Ω (baseAut x))
    (n : ℕ+) (hn : ((n : ℕ) : L) ≠ 0)
    (x : Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) :
    ContinuousCohomology.map (separableKummerConjugationPullback L baseAut lift hlift)
      (separableKummerConjugationCoefficient L baseAut lift hlift n) 1
      (Multiplicative.toAdd (separableMuH1EquivPowerClasses L n hn x)) =
      Multiplicative.toAdd (separableMuH1EquivPowerClasses L n hn
        (separableKummerPowerClassConjugation L baseAut n x)) := by
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective ((powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) x
  exact separableKummerH1Class_conjugation L baseAut lift hlift n hn a

end ClassFieldTheory.Brauer
