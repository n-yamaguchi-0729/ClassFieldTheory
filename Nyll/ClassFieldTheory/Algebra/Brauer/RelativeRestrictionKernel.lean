/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.Algebra.Brauer.EmbeddedInflation
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRestrictionKernel
public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction

/-! # The actual relative Brauer kernel for an abstract finite Galois extension -/

@[expose] public section

noncomputable section

open CategoryTheory ContRepresentation ContinuousCohomology

namespace ClassFieldTheory.Brauer

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Inflate the original relative classes through the specified embedding
of the finite Galois extension in the separable closure. -/
noncomputable def relativeInflationOfEmbedding (i : L →ₐ[K] SeparableClosure K) :
    continuousCohomology 2 (galoisUnitsRep K L) →+ Br K :=
  transportCohomology 2 (embeddedGaloisRestriction (B := K) i) i.toRingHom
    (embeddedGaloisRestriction_commutes (B := K) i)

/-- An absolute class split by the original finite Galois extension is
inflated using any specified embedding of that extension. -/
theorem exists_relativeInflationOfEmbedding_eq_of_restrict_eq_zero
    (i : L →ₐ[K] SeparableClosure K) (b : Br K)
    (hb : restrict (algebraMap K L) b = 0) :
    ∃ a : continuousCohomology 2 (galoisUnitsRep K L), relativeInflationOfEmbedding i a = b := by
  let F : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    i.finiteGaloisFieldRange
  let j : L ≃ₐ[K] F := i.equivFieldRange
  let : FiniteDimensional K F := F.finiteDimensional
  let : DiscreteTopology Gal(F/K) := krullTopology_discreteTopology_of_finiteDimensional K F
  let r : Gal(F/K) ≃ₜ* Gal(L/K) :=
    { toMulEquiv := AlgEquiv.autCongr j.symm
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have hr (σ : Gal(F/K)) (x : L) : j (r σ x) = σ (j x) := by
    change j (j.symm (σ (j x))) = σ (j x)
    exact j.apply_symm_apply _
  have hr' (σ : Gal(L/K)) (y : F) : j.symm (r.symm σ y) = σ (j.symm y) := by
    apply j.injective
    have hh := hr (r.symm σ) (j.symm y)
    rw [r.apply_symm_apply, j.apply_symm_apply] at hh
    rw [j.apply_symm_apply]
    exact hh.symm
  let s := embeddedGaloisRestriction (B := K) i
  let hs := embeddedGaloisRestriction_commutes (B := K) i
  have hgroups (σ : Gal(SeparableClosure K/K)) : r (finiteGaloisRestriction F σ) = s σ := by
    apply AlgEquiv.ext
    intro x
    apply i.injective
    exact (congrArg F.toIntermediateField.val (hr (finiteGaloisRestriction F σ) x)).trans
      ((finiteGaloisRestriction_commutes F σ (j x)).trans (hs σ x).symm)
  let T := transportCohomology 2 (ContinuousMonoidHom.toContinuousMonoidHom r) j.toRingHom hr
  let T' := transportCohomology 2 (ContinuousMonoidHom.toContinuousMonoidHom r.symm)
    j.symm.toRingHom hr'
  have hfactor (a : continuousCohomology 2 (galoisUnitsRep K L)) :
      relativeInflationOfEmbedding i a = finiteInflation F (T a) := by
    have hcomp := galoisUnitsCohomologyMap_comp (ContinuousMonoidHom.toContinuousMonoidHom r)
      (finiteGaloisRestriction F) s j.toRingHom F.toIntermediateField.val.toRingHom
      i.toRingHom hr (finiteGaloisRestriction_commutes F) hs hgroups (fun _ => rfl)
    change ContinuousCohomology.map s (galoisUnitsMap s i.toRingHom hs) 2 a =
      ContinuousCohomology.map (finiteGaloisRestriction F) (finiteInflationCoefficientMap F) 2
        (ContinuousCohomology.map (ContinuousMonoidHom.toContinuousMonoidHom r)
          (galoisUnitsMap (ContinuousMonoidHom.toContinuousMonoidHom r) j.toRingHom hr) 2 a)
    exact ConcreteCategory.congr_hom hcomp a
  have hj : j.toRingHom.comp (algebraMap K L) = algebraMap K F := RingHom.ext j.commutes
  have hcomp := (restrict_comp (algebraMap K L) j.toRingHom).trans
    (congrArg (fun f : K →+* F => restrict f) hj)
  have hf : restrict (algebraMap K F) b = 0 := by
    calc
      _ = restrict j.toRingHom (restrict (algebraMap K L) b) := (DFunLike.congr_fun hcomp b).symm
      _ = 0 := by rw [hb, map_zero]
  obtain ⟨x, hx⟩ := exists_finiteInflation_of_restrict_eq_zero F b hf
  have hT : T (T' x) = x :=
    transportCohomology_leftInverse_of_equiv r.symm j.symm hr' hr x
  refine ⟨T' x, ?_⟩
  rw [hfactor, hT]
  exact hx

end ClassFieldTheory.Brauer
