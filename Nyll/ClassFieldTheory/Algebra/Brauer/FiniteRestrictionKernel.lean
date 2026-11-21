/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.EmbeddedInflation
public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction

/-! # Finite inflation identifies the kernel of actual Brauer restriction -/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousCohomology ClassFieldTower.Cohomology

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K]

section StageRestriction

variable (E : IntermediateField K (SeparableClosure K))
    (N : FiniteGaloisIntermediateField K (SeparableClosure K))
    [Algebra E N] [IsScalarTower K E N] [IsScalarTower E N (SeparableClosure K)]
    [FiniteDimensional E N]

private noncomputable def stageBaseClosureEquiv :
    SeparableClosure K ≃ₐ[E] SeparableClosure E := by
  let Ω := SeparableClosure K
  let : IsSepClosure E Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ω⟩
  exact IsSepClosure.equiv E Ω (SeparableClosure E)

private noncomputable def stageClosurePullback :
    Gal(SeparableClosure E/E) →ₜ* Gal(SeparableClosure K/K) := by
  let b : Gal(SeparableClosure K/E) →ₜ* Gal(SeparableClosure K/K) :=
    { toMonoidHom := AlgEquiv.restrictScalarsHom K
      continuous_toFun := InfiniteGalois.restrictScalarsHom_continuous K E (SeparableClosure K) }
  exact b.comp (ContinuousMonoidHom.toContinuousMonoidHom
    (KummerTheory.galoisClosureTransport (stageBaseClosureEquiv E).symm))

private theorem stageClosurePullback_commutes (σ : Gal(SeparableClosure E/E))
    (a : SeparableClosure K) :
    stageBaseClosureEquiv E (stageClosurePullback E σ a) = σ (stageBaseClosureEquiv E a) :=
  (stageBaseClosureEquiv E).apply_symm_apply _

private theorem stageBaseClosureEquiv_commutes (a : K) :
    stageBaseClosureEquiv E (algebraMap K (SeparableClosure K) a) =
      algebraMap E (SeparableClosure E) (algebraMap K E a) := by
  have he := IsScalarTower.algebraMap_apply K E (SeparableClosure K) a
  exact (congrArg (stageBaseClosureEquiv E) he).trans
    ((stageBaseClosureEquiv E).commutes (algebraMap K E a))

private noncomputable def stageUnitEmbedding : N →ₐ[E] SeparableClosure E :=
  let j := stageBaseClosureEquiv E
  j.toAlgHom.comp
    { __ := N.toIntermediateField.val.toRingHom
      commutes' a := (IsScalarTower.algebraMap_apply E N (SeparableClosure K) a).symm }

omit [IsScalarTower K E N] [FiniteDimensional E N] in
private theorem stageUnitEmbedding_apply (a : N) :
    stageUnitEmbedding E N a = stageBaseClosureEquiv E (a : SeparableClosure K) := rfl

private theorem stageRestriction_groupFactor [Normal E N] (σ : Gal(SeparableClosure E/E)) :
    relativeBaseRestrictionHom K E N
        (embeddedGaloisRestriction (B := E) (stageUnitEmbedding E N) σ) =
      finiteGaloisRestriction N (stageClosurePullback E σ) := by
  let i := stageUnitEmbedding E N
  let s := embeddedGaloisRestriction (B := E) i
  let r := relativeBaseRestrictionHom K E N
  apply AlgEquiv.ext
  intro a
  apply i.injective
  change i (r (s σ) a) = i (finiteGaloisRestriction N (stageClosurePullback E σ) a)
  have hi := embeddedGaloisRestriction_commutes (B := E) i σ a
  exact hi.trans ((stageClosurePullback_commutes E σ a).symm.trans
    (congrArg (stageBaseClosureEquiv E)
      (finiteGaloisRestriction_commutes N (stageClosurePullback E σ) a).symm))

private noncomputable def stageAbsoluteInflation [Normal E N] :
    continuousCohomology 2 (galoisUnitsRep E N) →+ Br E :=
  let i := stageUnitEmbedding E N
  transportCohomology 2 (embeddedGaloisRestriction (B := E) i) i.toRingHom
    (embeddedGaloisRestriction_commutes (B := E) i)

omit [IsScalarTower K E N] in
private theorem stageAbsoluteInflation_injective [IsGalois E N] :
    Function.Injective (stageAbsoluteInflation E N) :=
  embeddedInflation_injective (A := E) (B := E) (M := N)
    (fun a : E => ⟨a, rfl⟩) (stageUnitEmbedding E N)

private theorem restrict_finiteInflation_eq_stageAbsoluteInflation [Normal E N] (x : relativeBr N) :
    restrict (algebraMap K E) (finiteInflation N x) =
      stageAbsoluteInflation E N (relativeBaseRestriction K E N x) := by
  let q := stageClosurePullback E
  let j := stageBaseClosureEquiv E
  let i := stageUnitEmbedding E N
  let hq := stageClosurePullback_commutes E
  let s := embeddedGaloisRestriction (B := E) i
  let hs := embeddedGaloisRestriction_commutes (B := E) i
  let r := relativeBaseRestrictionHom K E N
  let φ := galoisUnitsMap r (RingHom.id N) (fun _ _ => rfl)
  obtain ⟨z, rfl⟩ := π_surjective (galoisUnitsRep K N) 2 x
  let y := π (galoisUnitsRep K N) 2 z
  have hdefault := restrictOfEmbedding_eq_of_extends (algebraMap K E) q j.toRingHom
    (stageBaseClosureEquiv_commutes E) hq
  rw [← hdefault]
  have hπ : ContinuousCohomology.map r φ 2 y =
      π (galoisUnitsRep E N) 2 (cocyclesMap r φ 2 z) :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  have hfactor := restrictOfEmbedding_finiteInflation_eq_of_factor N q j.toRingHom hq
    r (RingHom.id N) (fun _ _ => rfl) s i.toRingHom hs
    (stageRestriction_groupFactor E N) (stageUnitEmbedding_apply E N) z
  exact hfactor.trans (congrArg (fun a => stageAbsoluteInflation E N a) hπ.symm)

/-- Restricting a class from a finite stage detects its relative restriction
over the intermediate base. -/
theorem restrict_finiteInflation_eq_zero_iff_relativeBaseRestriction (x : relativeBr N) :
    restrict (algebraMap K E) (finiteInflation N x) = 0 ↔ relativeBaseRestriction K E N x = 0 := by
  let : IsGalois E N := IsGalois.tower_top_of_isGalois K E N
  rw [restrict_finiteInflation_eq_stageAbsoluteInflation E N]
  exact ⟨fun h => stageAbsoluteInflation_injective E N
    (h.trans (map_zero (stageAbsoluteInflation E N)).symm), fun h => by rw [h, map_zero]⟩

end StageRestriction

/-- Every actual absolute class split by a finite Galois stage comes from that stage. -/
theorem exists_finiteInflation_of_restrict_eq_zero
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (x : Br K)
    (h : restrict (algebraMap K E) x = 0) :
    ∃ y : relativeBr E, finiteInflation E y = x := by
  obtain ⟨F, y, hy⟩ := exists_finiteInflation_eq x
  let N := E ⊔ F
  have hEN : E.toIntermediateField ≤ N.toIntermediateField :=
    (FiniteGaloisIntermediateField.le_iff E N).mp le_sup_left
  have hFN : F.toIntermediateField ≤ N.toIntermediateField :=
    (FiniteGaloisIntermediateField.le_iff F N).mp le_sup_right
  let : Algebra E N := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
  let : Algebra F N := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
  let : IsScalarTower K E N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K F N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower E N (SeparableClosure K) := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E N := FiniteDimensional.right K E N
  let w := relativeInflation K F N y
  have hw : finiteInflation N w = x :=
    (finiteInflation_tower F N (fun _ => rfl) y).trans hy
  have hrestrict : relativeBaseRestriction K E N w = 0 :=
    (restrict_finiteInflation_eq_zero_iff_relativeBaseRestriction E.toIntermediateField N w).mp
      ((congrArg (restrict (algebraMap K E)) hw).trans h)
  have hzero : liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (continuousRelativeUnitsH2Equiv K N w) = 0 := by
    rw [← continuousRelativeUnitsH2Equiv_baseRestriction, hrestrict, map_zero]
  obtain ⟨b, hb⟩ := liftedFiniteGaloisTowerUnitsH2Restriction_ker_le_inflation_range K E N hzero
  let z := (continuousRelativeUnitsH2Equiv K E).symm b
  have hz : relativeInflation K E N z = w := by
    apply (continuousRelativeUnitsH2Equiv K N).injective
    rw [continuousRelativeUnitsH2Equiv_inflation, show continuousRelativeUnitsH2Equiv K E z = b from
      (continuousRelativeUnitsH2Equiv K E).apply_symm_apply b]
    exact hb
  exact ⟨z, (finiteInflation_tower E N (fun _ => rfl) z).symm.trans
    ((congrArg (finiteInflation N) hz).trans hw)⟩

/-- A relative class becomes trivial over its original upper field. -/
theorem restrict_finiteInflation_eq_zero
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (x : relativeBr E) :
    restrict (algebraMap K E) (finiteInflation E x) = 0 := by
  apply (restrict_finiteInflation_eq_zero_iff_relativeBaseRestriction E.toIntermediateField E x).mpr
  have : Subsingleton Gal(E/E) := by
    constructor
    intro σ τ
    apply AlgEquiv.ext
    intro a
    exact (σ.commutes a).trans (τ.commutes a).symm
  have hsub : Subsingleton (groupCohomology (liftedGaloisUnitsRep E E) 2) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton (liftedGaloisUnitsRep E E) 1)
  exact (continuousRelativeUnitsH2Equiv E E).injective (hsub.elim _ _)

/-- The image of actual finite inflation is the kernel of restriction to its splitting field. -/
theorem finiteInflation_range_eq_ker (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    (finiteInflation E).range = (restrict (algebraMap K E)).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact restrict_finiteInflation_eq_zero E y
  · exact exists_finiteInflation_of_restrict_eq_zero E x

end ClassFieldTheory.Brauer
