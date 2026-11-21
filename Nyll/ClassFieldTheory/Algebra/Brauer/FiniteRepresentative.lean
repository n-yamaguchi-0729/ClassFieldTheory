/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteInflation
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCrossedHom
public import Nyll.GaloisCohomology.Topology.GaloisFiniteStageTuples

/-!
# Finite Galois representatives of Brauer cochains

Compactness gives one finite Galois stage for the tuple arguments. Homogeneous
equivariance then forces the values to be fixed by the kernel of restriction,
so the same stage supplies the coefficient units.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopRep

namespace ClassFieldTheory.Brauer

variable {K : Type u} [Field K]

/-- Inclusion of the stage's original multiplicative coefficients, written additively. -/
def finiteUnitInclusion (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    Additive Eˣ →+ Additive (SeparableClosure K)ˣ :=
  (Units.map E.toIntermediateField.val.toMonoidHom).toAdditive

theorem finiteUnitInclusion_injective (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    Function.Injective (finiteUnitInclusion E) :=
  Units.map_injective E.toIntermediateField.val.injective

/-- Actual homogeneous cochains on separable-closure units use arguments and
unit values from one finite Galois stage. -/
theorem exists_finiteUnitsRepresentative (n : ℕ) (z : (homogeneousCochains (unitsRep K)).X n) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
      (f : (Fin (n + 1) → Gal(E/K)) → Additive Eˣ),
      ∀ a : Fin (n + 1) → Gal(SeparableClosure K/K),
        finiteUnitInclusion E (f (fun i => finiteGaloisRestriction E (a i))) =
          resolutionTupleHomeomorph Gal(SeparableClosure K/K) (unitsRep K) (n + 1) z.val a := by
  let G := Gal(SeparableClosure K/K)
  let c : C(Fin (n + 1) → G, unitsRep K) :=
    resolutionTupleHomeomorph G (unitsRep K) (n + 1) z.val
  obtain ⟨E, cE, hcE⟩ := GaloisCohomology.exists_finiteGalois_factor_continuous_tuple_discrete
    (fun a : Fin (n + 1) → G => c a) c.continuous
  let r := finiteGaloisRestriction E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective (SeparableClosure K)
  have hfactor (a : Fin (n + 1) → G) : cE (fun i => r (a i)) = c a := hcE a
  have hfixed (b : Fin (n + 1) → Gal(E/K)) (τ : G) (hτ : τ ∈ E.fixingSubgroup) :
      (unitsRep K).ρ τ (cE b) = cE b := by
    let a : Fin (n + 1) → G := fun i => (hr (b i)).choose
    have ha : (fun i => r (a i)) = b := funext fun i => (hr (b i)).choose_spec
    have hker : r τ = 1 := by
      change τ ∈ (AlgEquiv.restrictNormalHom E.toIntermediateField).ker
      rwa [E.toIntermediateField.restrictNormalHom_ker]
    have hb : (fun i => r (τ * a i)) = b := by
      funext i
      rw [map_mul, hker, one_mul]
      exact congrFun ha i
    have h₁ : cE b = c a := by rw [← ha]; exact hfactor a
    have h₂ : cE b = c (fun i => τ * a i) := by rw [← hb]; exact hfactor _
    calc
      (unitsRep K).ρ τ (cE b) = (unitsRep K).ρ τ (c a) :=
        congrArg ((unitsRep K).ρ τ) h₁
      _ = c (fun i => τ * a i) :=
        (homogeneousCochain_tuple_equivariant G (unitsRep K) n z τ a).symm
      _ = cE b := h₂.symm
  let val (b : Fin (n + 1) → Gal(E/K)) : (SeparableClosure K)ˣ :=
    (show Additive (SeparableClosure K)ˣ from cE b).toMul
  have hmem (b : Fin (n + 1) → Gal(E/K)) :
      (val b : SeparableClosure K) ∈ E.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField,
      IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact congrArg (fun x : unitsRep K =>
      ((show Additive (SeparableClosure K)ˣ from x).toMul : SeparableClosure K))
      (hfixed b τ hτ)
  let f (b : Fin (n + 1) → Gal(E/K)) : Additive Eˣ :=
    Additive.ofMul (Units.mk0 ⟨(val b : SeparableClosure K), hmem b⟩
      (fun h => Units.ne_zero (val b) (congrArg Subtype.val h)))
  refine ⟨E, f, fun a => ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change (val (fun i => r (a i)) : SeparableClosure K) =
    ((show Additive (SeparableClosure K)ˣ from c a).toMul : SeparableClosure K)
  exact congrArg (fun x : unitsRep K =>
    ((show Additive (SeparableClosure K)ˣ from x).toMul : SeparableClosure K)) (hfactor a)

theorem cochain_cocycle_injective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : TopRep.{u} ℤ G) (n : ℕ) :
    Function.Injective ((homogeneousCochains X).iCycles n) := by
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  exact (ModuleCat.mono_iff_injective (F.map ((homogeneousCochains X).iCycles n))).mp inferInstance

private theorem finiteInflationCochain_injective
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (n : ℕ) :
    Function.Injective ((ContinuousCohomology.cochainsMap
      (finiteGaloisRestriction E) (finiteInflationCoefficientMap E)).f n) := by
  let G := Gal(SeparableClosure K/K)
  let H := Gal(E/K)
  let X := unitsRep K
  let Y := galoisUnitsRep K E
  let r := finiteGaloisRestriction E
  let φ := finiteInflationCoefficientMap E
  let F := ContinuousCohomology.cochainsMap r φ
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective (SeparableClosure K)
  intro w w' hw
  apply Subtype.ext
  apply (resolutionTupleHomeomorph H Y (n + 1)).injective
  apply ContinuousMap.ext
  intro b
  let a : Fin (n + 1) → G := fun i => (hr (b i)).choose
  have ha : (fun i => r (a i)) = b := funext fun i => (hr (b i)).choose_spec
  have hvalues : resolutionTupleHomeomorph G X (n + 1) ((F.f n) w).val a =
      resolutionTupleHomeomorph G X (n + 1) ((F.f n) w').val a :=
    congrArg (fun c : (homogeneousCochains X).X n =>
      resolutionTupleHomeomorph G X (n + 1) c.val a) hw
  have hleft := resolutionTupleHomeomorph_cochainsMap H Y X r φ n w a
  have hright := resolutionTupleHomeomorph_cochainsMap H Y X r φ n w' a
  change resolutionTupleHomeomorph H Y (n + 1) w.val b =
    resolutionTupleHomeomorph H Y (n + 1) w'.val b
  apply finiteUnitInclusion_injective E
  rw [ha] at hleft hright
  exact hleft.symm.trans (hvalues.trans hright)

private theorem finiteInflationCochain_eq
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (n : ℕ)
    (z₀ : (homogeneousCochains (unitsRep K)).X n)
    (w₀ : (homogeneousCochains (galoisUnitsRep K E)).X n)
    (h : ∀ a : Fin (n + 1) → Gal(SeparableClosure K/K),
      finiteUnitInclusion E (resolutionTupleHomeomorph Gal(E/K) (galoisUnitsRep K E) (n + 1)
        w₀.val (fun i => finiteGaloisRestriction E (a i))) =
      resolutionTupleHomeomorph Gal(SeparableClosure K/K) (unitsRep K) (n + 1) z₀.val a) :
    ((ContinuousCohomology.cochainsMap
      (finiteGaloisRestriction E) (finiteInflationCoefficientMap E)).f n) w₀ = z₀ := by
  apply Subtype.ext
  apply (resolutionTupleHomeomorph Gal(SeparableClosure K/K) (unitsRep K) (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  exact (resolutionTupleHomeomorph_cochainsMap Gal(E/K) (galoisUnitsRep K E) (unitsRep K)
    (finiteGaloisRestriction E) (finiteInflationCoefficientMap E) n w₀ a).trans (h a)

private theorem cochainMap_value_differential
    {C D : CochainComplex (TopModuleCat ℤ) ℕ} (F : HomologicalComplex.Hom C D) (n : ℕ) (w : C.X n) :
    (F.f (n + 1)).hom ((C.d n (n + 1)).hom w) = (D.d n (n + 1)).hom ((F.f n).hom w) :=
  (ConcreteCategory.congr_hom (F.comm n (n + 1)) w).symm

private theorem finiteUnitsRepresentative_closed (n : ℕ)
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (z₀ : (homogeneousCochains (unitsRep K)).X n)
    (w₀ : (homogeneousCochains (galoisUnitsRep K E)).X n)
    (hz : (homogeneousCochains (unitsRep K)).d n (n + 1) z₀ = 0)
    (h : ∀ a : Fin (n + 1) → Gal(SeparableClosure K/K),
      finiteUnitInclusion E (resolutionTupleHomeomorph Gal(E/K) (galoisUnitsRep K E) (n + 1)
        w₀.val (fun i => finiteGaloisRestriction E (a i))) =
      resolutionTupleHomeomorph Gal(SeparableClosure K/K) (unitsRep K) (n + 1) z₀.val a) :
    (homogeneousCochains (galoisUnitsRep K E)).d n (n + 1) w₀ = 0 := by
  let F := ContinuousCohomology.cochainsMap
    (finiteGaloisRestriction E) (finiteInflationCoefficientMap E)
  have hinj : Function.Injective (F.f (n + 1)) := finiteInflationCochain_injective E (n + 1)
  apply hinj
  change (F.f (n + 1)).hom (((homogeneousCochains (galoisUnitsRep K E)).d n (n + 1)).hom w₀) =
    (F.f (n + 1)).hom 0
  rw [cochainMap_value_differential F n w₀]
  have hstage : (F.f n).hom w₀ = z₀ := finiteInflationCochain_eq E n z₀ w₀ h
  rw [hstage]
  exact hz.trans (map_zero (F.f (n + 1)).hom).symm

private theorem finiteUnitsRepresentative_cocycle (n : ℕ)
    (z : ContinuousCohomology.cocycles (unitsRep K) n)
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (f : (Fin (n + 1) → Gal(E/K)) → Additive Eˣ)
    (hf : ∀ a : Fin (n + 1) → Gal(SeparableClosure K/K),
      finiteUnitInclusion E (f (fun i => finiteGaloisRestriction E (a i))) =
        resolutionTupleHomeomorph Gal(SeparableClosure K/K) (unitsRep K) (n + 1)
          ((homogeneousCochains (unitsRep K)).iCycles n z).val a) :
    ∃ w : ContinuousCohomology.cocycles (galoisUnitsRep K E) n,
      ∀ b : Fin (n + 1) → Gal(E/K),
        resolutionTupleHomeomorph Gal(E/K) (galoisUnitsRep K E) (n + 1)
          ((homogeneousCochains (galoisUnitsRep K E)).iCycles n w).val b = f b := by
  let G := Gal(SeparableClosure K/K)
  let X := unitsRep K
  let z₀ : (homogeneousCochains X).X n := (homogeneousCochains X).iCycles n z
  let c : C(Fin (n + 1) → G, X) := resolutionTupleHomeomorph G X (n + 1) z₀.val
  let H := Gal(E/K)
  let Y := galoisUnitsRep K E
  let r := finiteGaloisRestriction E
  let ι : Y →+ X := finiteUnitInclusion E
  have hinj : Function.Injective ι := finiteUnitInclusion_injective E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective (SeparableClosure K)
  let lift (b : H) : G := (hr b).choose
  have hlift (b : H) : r (lift b) = b := (hr b).choose_spec
  have hfac (a : Fin (n + 1) → G) : ι (f (fun i => r (a i))) = c a := hf a
  have hact (σ : G) (a : Y) : ι (Y.ρ (r σ) a) = X.ρ σ (ι a) := by
    apply Units.ext
    exact finiteGaloisRestriction_commutes E σ ((show Additive Eˣ from a).toMul : E)
  let f' : C(Fin (n + 1) → H, Y) := ⟨f, continuous_of_discreteTopology⟩
  have hequiv (τ : H) (b : Fin (n + 1) → H) : f' (fun i => τ * b i) = Y.ρ τ (f' b) := by
    obtain ⟨σ, rfl⟩ := hr τ
    let a : Fin (n + 1) → G := lift ∘ b
    have ha : (fun i => r (a i)) = b := funext fun i => hlift (b i)
    have hb : (fun i => r (σ * a i)) = (fun i => r σ * b i) := by
      funext i
      rw [map_mul, congrFun ha i]
    apply hinj
    change ι (f (fun i => r σ * b i)) = ι (Y.ρ (r σ) (f b))
    have hvalue : ι (f b) = c a := (congrArg (fun p => ι (f p)) ha).symm.trans (hfac a)
    calc
      _ = c (fun i => σ * a i) :=
        (congrArg (fun p => ι (f p)) hb).symm.trans (hfac (fun i => σ * a i))
      _ = X.ρ σ (c a) := homogeneousCochain_tuple_equivariant G X n z₀ σ a
      _ = X.ρ σ (ι (f b)) := congrArg (X.ρ σ) hvalue.symm
      _ = _ := (hact σ (f b)).symm
  let w₀ := homogeneousCochainOfTuple H Y n f' hequiv
  have hw (b : Fin (n + 1) → H) : resolutionTupleHomeomorph H Y (n + 1) w₀.val b = f b :=
    congrArg (fun f₀ : C(Fin (n + 1) → H, Y) => f₀ b)
      (homogeneousCochainOfTuple_apply H Y n f' hequiv)
  have hz : (homogeneousCochains X).d n (n + 1) z₀ = 0 :=
    ConcreteCategory.congr_hom ((homogeneousCochains X).iCycles_d n (n + 1)) z
  have hcompare (a : Fin (n + 1) → G) :
      ι (resolutionTupleHomeomorph H Y (n + 1) w₀.val (fun i => r (a i))) = c a :=
    (congrArg ι (hw (fun i => r (a i)))).trans (hfac a)
  have hwzero : (homogeneousCochains Y).d n (n + 1) w₀ = 0 :=
    finiteUnitsRepresentative_closed n E z₀ w₀ hz hcompare
  let line := ContinuousCohomology.CrossedHom.scalarLine w₀
  have hline : line ≫ (homogeneousCochains Y).d n (n + 1) = 0 :=
    ContinuousCohomology.CrossedHom.scalarLine_comp_eq_zero w₀ _ hwzero
  let w : ContinuousCohomology.cocycles Y n :=
    ((homogeneousCochains Y).liftCycles line (n + 1) (CochainComplex.next ℕ n) hline) (ULift.up 1)
  have hwcycle : (homogeneousCochains Y).iCycles n w = w₀ := by
    change (homogeneousCochains Y).iCycles n
      (((homogeneousCochains Y).liftCycles line (n + 1) (CochainComplex.next ℕ n) hline)
        (ULift.up 1)) = _
    rw [← ConcreteCategory.comp_apply, (homogeneousCochains Y).liftCycles_i]
    exact ContinuousCohomology.CrossedHom.scalarLine_one w₀
  refine ⟨w, fun b => ?_⟩
  change resolutionTupleHomeomorph H Y (n + 1) ((homogeneousCochains Y).iCycles n w).val b = f b
  rw [hwcycle]
  exact hw b

/-- In every degree, an actual class on separable-closure units is inflated
from the unit cohomology of a finite Galois subextension. -/
theorem exists_finiteDegreeInflation_eq (n : ℕ) (x : continuousCohomology n (unitsRep K)) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
      (y : continuousCohomology n (galoisUnitsRep K E)),
      finiteDegreeInflation E n y = x := by
  let G := Gal(SeparableClosure K/K)
  let X := unitsRep K
  obtain ⟨z, rfl⟩ := ContinuousCohomology.π_surjective X n x
  obtain ⟨E, f, hf⟩ := exists_finiteUnitsRepresentative n ((homogeneousCochains X).iCycles n z)
  obtain ⟨w, hw⟩ := finiteUnitsRepresentative_cocycle n z E f hf
  refine ⟨E, ContinuousCohomology.π (galoisUnitsRep K E) n w, ?_⟩
  rw [finiteDegreeInflation_π]
  apply congrArg (ContinuousCohomology.π X n)
  apply cochain_cocycle_injective X n
  rw [ContinuousCohomology.cochainOfMappedCocycle]
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G X (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  rw [resolutionTupleHomeomorph_cochainsMap, hw]
  exact hf a

/-- Every absolute Brauer class is inflated from an actual finite Galois
subextension of the separable closure. -/
theorem exists_finiteInflation_eq (x : Br K) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (y : relativeBr E),
      finiteInflation E y = x :=
  exists_finiteDegreeInflation_eq 2 x

end ClassFieldTheory.Brauer
