/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteInflationExactness
public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction

/-! # Inflation from an embedded extension of an isomorphic base field -/

@[expose] public section

noncomputable section

universe u

open CategoryTheory ContRepresentation TopRep ContinuousCohomology

namespace ClassFieldTheory.Brauer

section Transport

variable {K L E F : Type u} [Field K] [Field L] [Field E] [Field F]
    [Algebra K E] [Algebra L F]

/-- Transport by an equivariant isomorphism is inverted by transport through
its original inverse group and field maps. -/
theorem transportCohomology_leftInverse_of_equiv
    (r : Gal(F/L) ≃ₜ* Gal(E/K)) (j : E ≃+* F)
    (h : ∀ (σ : Gal(F/L)) (x : E), j (r σ x) = σ (j x))
    (hr : ∀ (σ : Gal(E/K)) (y : F), j.symm (r.symm σ y) = σ (j.symm y)) :
    Function.LeftInverse
      (transportCohomology 2 (ContinuousMonoidHom.toContinuousMonoidHom r.symm) j.symm.toRingHom hr)
      (transportCohomology 2 (ContinuousMonoidHom.toContinuousMonoidHom r) j.toRingHom h) := by
  intro x
  let d := ContinuousMonoidHom.id Gal(E/K)
  let φ := galoisUnitsMap d (RingHom.id E) (fun _ _ => rfl)
  have hφ : φ = 𝟙 (galoisUnitsRep K E) := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro a
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  have hid : ContinuousCohomology.map d φ 2 = 𝟙 (continuousCohomology 2 (galoisUnitsRep K E)) :=
    (congrArg (fun a => ContinuousCohomology.map d a 2) hφ).trans
      (ContinuousCohomology.map_id (galoisUnitsRep K E) 2)
  have hcomp := galoisUnitsCohomologyMap_comp (ContinuousMonoidHom.toContinuousMonoidHom r)
    (ContinuousMonoidHom.toContinuousMonoidHom r.symm)
    d j.toRingHom j.symm.toRingHom (RingHom.id E) h hr (fun _ _ => rfl)
    r.apply_symm_apply j.symm_apply_apply
  change ContinuousCohomology.map (ContinuousMonoidHom.toContinuousMonoidHom r.symm)
      (galoisUnitsMap (ContinuousMonoidHom.toContinuousMonoidHom r.symm) j.symm.toRingHom hr) 2
      (ContinuousCohomology.map (ContinuousMonoidHom.toContinuousMonoidHom r)
        (galoisUnitsMap (ContinuousMonoidHom.toContinuousMonoidHom r) j.toRingHom h) 2 x) = x
  exact ConcreteCategory.congr_hom (hcomp.symm.trans hid) x

private theorem transportCohomology_injective_of_equiv
    (r : Gal(F/L) ≃ₜ* Gal(E/K)) (j : E ≃+* F)
    (h : ∀ (σ : Gal(F/L)) (x : E), j (r σ x) = σ (j x)) :
    Function.Injective
      (transportCohomology 2 (ContinuousMonoidHom.toContinuousMonoidHom r) j.toRingHom h) := by
  have hr (σ : Gal(E/K)) (y : F) : j.symm (r.symm σ y) = σ (j.symm y) := by
    apply j.injective
    have hh := h (r.symm σ) (j.symm y)
    rw [r.apply_symm_apply, j.apply_symm_apply] at hh
    rw [j.apply_symm_apply]
    exact hh.symm
  exact (transportCohomology_leftInverse_of_equiv r j h hr).injective

end Transport

variable {A B M : Type u} [Field A] [Field B] [Field M]

section AbsoluteInflation

variable
    [Algebra A M] [Algebra A B] [Algebra A (SeparableClosure B)]
    [IsScalarTower A B (SeparableClosure B)] [FiniteDimensional A M] [IsGalois A M]

/-- Inflation of the actual relative classes of an embedded finite normal
extension is injective when the original scalar map of the bases is onto. -/
theorem embeddedInflation_injective (h : Function.Surjective (algebraMap A B))
    (i : M →ₐ[A] SeparableClosure B) :
    Function.Injective (ContinuousCohomology.map
      (embeddedGaloisRestriction (B := B) i)
      (galoisUnitsMap (embeddedGaloisRestriction (B := B) i) i.toRingHom
        (embeddedGaloisRestriction_commutes (B := B) i)) 2) := by
  let e : A ≃+* B := RingEquiv.ofBijective (algebraMap A B) ⟨(algebraMap A B).injective, h⟩
  let : Algebra B M := ((algebraMap A M).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun a =>
    congrArg (algebraMap A M) (e.symm_apply_apply a).symm
  let iB : M →ₐ[B] SeparableClosure B :=
    { __ := i.toRingHom
      commutes' b := by
        obtain ⟨a, rfl⟩ := h b
        rw [← IsScalarTower.algebraMap_apply A B M,
          ← IsScalarTower.algebraMap_apply A B (SeparableClosure B)]
        exact i.commutes a }
  have : FiniteDimensional B M := FiniteDimensional.right A B M
  have : IsGalois B M := IsGalois.tower_top_of_isGalois A B M
  let F : FiniteGaloisIntermediateField B (SeparableClosure B) :=
    iB.finiteGaloisFieldRange
  let j : M ≃ₐ[B] F := iB.equivFieldRange
  let re : Gal(F/B) ≃* Gal(M/A) :=
    (AlgEquiv.autCongr j.symm).trans (AlgEquiv.extendScalarsHomOfSurjective (A := M) h).symm
  let : FiniteDimensional B F := F.finiteDimensional
  let : DiscreteTopology Gal(F/B) := krullTopology_discreteTopology_of_finiteDimensional B F
  let : DiscreteTopology Gal(M/A) := krullTopology_discreteTopology_of_finiteDimensional A M
  let r : Gal(F/B) ≃ₜ* Gal(M/A) :=
    { toMulEquiv := re
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have hr (σ : Gal(F/B)) (x : M) : j (r σ x) = σ (j x) := by
    change j (j.symm (σ (j x))) = σ (j x)
    exact j.apply_symm_apply _
  let s := embeddedGaloisRestriction (B := B) i
  let hs := embeddedGaloisRestriction_commutes (B := B) i
  have hgroups (σ : Gal(SeparableClosure B/B)) : r (finiteGaloisRestriction F σ) = s σ := by
    ext x
    apply i.injective
    have hcomp := congrArg F.toIntermediateField.val (hr (finiteGaloisRestriction F σ) x)
    exact hcomp.trans ((finiteGaloisRestriction_commutes F σ (j x)).trans (hs σ x).symm)
  let T := transportCohomology 2 (ContinuousMonoidHom.toContinuousMonoidHom r) j.toRingHom hr
  let I := ContinuousCohomology.map s (galoisUnitsMap s i.toRingHom hs) 2
  have hfactor (x : continuousCohomology 2 (galoisUnitsRep A M)) :
      I x = finiteInflation F (T x) := by
    have hcomp := galoisUnitsCohomologyMap_comp (ContinuousMonoidHom.toContinuousMonoidHom r)
      (finiteGaloisRestriction F) s j.toRingHom F.toIntermediateField.val.toRingHom
      i.toRingHom hr (finiteGaloisRestriction_commutes F) hs hgroups (fun _ => rfl)
    change I x =
      ContinuousCohomology.map (finiteGaloisRestriction F) (finiteInflationCoefficientMap F) 2
        (ContinuousCohomology.map (ContinuousMonoidHom.toContinuousMonoidHom r)
          (galoisUnitsMap (ContinuousMonoidHom.toContinuousMonoidHom r) j.toRingHom hr) 2 x)
    exact ConcreteCategory.congr_hom hcomp x
  intro x y hxy
  apply transportCohomology_injective_of_equiv r j.toRingEquiv hr
  apply finiteInflation_injective F
  change finiteInflation F (T x) = finiteInflation F (T y)
  rw [← hfactor, ← hfactor]
  exact hxy

end AbsoluteInflation

section AbsoluteTransport

variable {K : Type u} [Field K] [Algebra K A] [Algebra K B]
    [Algebra A M] [FiniteDimensional A M] [IsGalois A M]

/-- Inflate the relative class of the original finite extension into the
absolute Brauer group of an isomorphic base. -/
def embeddedRelativeToAbsolute (e : A ≃ₐ[K] B) :
    continuousCohomology 2 (galoisUnitsRep A M) →+ Br B := by
  let Ω := SeparableClosure B
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Algebra A Ω := ((algebraMap B Ω).comp e.toRingHom).toAlgebra
  let : IsScalarTower A B Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let i : M →ₐ[A] Ω := IsSepClosed.lift
  let s := embeddedGaloisRestriction (B := B) i
  let φ := galoisUnitsMap s i.toRingHom (embeddedGaloisRestriction_commutes (B := B) i)
  exact (ContinuousCohomology.map s φ 2).hom.toLinearMap.toAddMonoidHom

/-- Inflation from the actual relative extension is injective. -/
theorem embeddedRelativeToAbsolute_injective (e : A ≃ₐ[K] B) :
    Function.Injective (embeddedRelativeToAbsolute (M := M) e) := by
  let Ω := SeparableClosure B
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Algebra A Ω := ((algebraMap B Ω).comp e.toRingHom).toAlgebra
  let : IsScalarTower A B Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let i : M →ₐ[A] Ω := IsSepClosed.lift
  exact embeddedInflation_injective e.surjective i

end AbsoluteTransport

section RestrictFromGlobal

variable {K : Type u} [Field K] [Algebra K A] [Algebra K B]
    [Algebra K M] [Algebra A M] [IsScalarTower K A M] [FiniteDimensional A M] [IsGalois A M]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))

/-- Restriction of a finite class through the original embedding of the chosen local field. -/
def embeddedRelativeRestriction (j : E →ₐ[K] M) : relativeBr E →+
      continuousCohomology 2 (galoisUnitsRep A M) :=
  transportCohomology 2 (embeddedGaloisRestriction (B := A) j) j.toRingHom
    (embeddedGaloisRestriction_commutes (B := A) j)

omit [FiniteDimensional A M] in
/-- Actual absolute restriction agrees with relative restriction followed
by inflation through the completed stage. -/
theorem restrict_finiteInflation_eq_embeddedRelativeRestriction (e : A ≃ₐ[K] B)
    (j₀ : E →ₐ[K] M) (x : relativeBr E) :
    restrict (algebraMap K B) (finiteInflation E x) =
      embeddedRelativeToAbsolute e (embeddedRelativeRestriction E j₀ x) := by
  obtain ⟨z, rfl⟩ := π_surjective (galoisUnitsRep K E) 2 x
  let Ω := SeparableClosure B
  let f := algebraMap K B
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Algebra A Ω := ((algebraMap B Ω).comp e.toRingHom).toAlgebra
  let : Algebra K Ω := ((algebraMap B Ω).comp f).toAlgebra
  have : IsScalarTower A B Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun a =>
    congrArg (algebraMap B Ω) (e.commutes a).symm
  let i : M →ₐ[A] Ω := IsSepClosed.lift
  let b₀ : E →ₐ[K] Ω :=
    { __ := (Field.absoluteGaloisGroup.separableClosureLift f).comp
        E.toIntermediateField.val.toRingHom
      commutes' := fun a => Field.absoluteGaloisGroup.separableClosureLift_algebraMap f a }
  obtain ⟨τ, hτ⟩ := ClassFieldTheory.exists_embedding_comp_aut_eq_of_normal b₀
    ((i.restrictScalars K).comp j₀)
  let j := j₀.comp τ.toAlgHom
  have hcoeff (a : E) : i (j a) = Field.absoluteGaloisGroup.separableClosureLift f a := hτ a
  let r := embeddedGaloisRestriction (B := A) j
  let s := embeddedGaloisRestriction (B := B) i
  have hr := embeddedGaloisRestriction_commutes (B := A) j
  have hs := embeddedGaloisRestriction_commutes (B := B) i
  have hgroups (g : Gal(Ω/B)) :
      r (s g) = finiteGaloisRestriction E (Field.absoluteGaloisGroup.separableMap f g) := by
    apply AlgEquiv.ext
    intro a
    apply E.toIntermediateField.val.injective
    apply (Field.absoluteGaloisGroup.separableClosureLift f).injective
    change Field.absoluteGaloisGroup.separableClosureLift f (r (s g) a) =
      Field.absoluteGaloisGroup.separableClosureLift f
        (finiteGaloisRestriction E (Field.absoluteGaloisGroup.separableMap f g) a)
    rw [← hcoeff (r (s g) a), hr, hs, hcoeff, finiteGaloisRestriction_commutes,
      Field.absoluteGaloisGroup.separableMap_commutes]
  let φ := galoisUnitsMap r j.toRingHom hr
  let I := ContinuousCohomology.map s (galoisUnitsMap s i.toRingHom hs) 2
  let r₀ := embeddedGaloisRestriction (B := A) j₀
  let φ₀ := galoisUnitsMap r₀ j₀.toRingHom (embeddedGaloisRestriction_commutes (B := A) j₀)
  have hmap : ContinuousCohomology.map r φ 2 = ContinuousCohomology.map r₀ φ₀ 2 :=
    relativeCohomologyMap_comp_aut τ j₀.toRingHom r₀ r
      (embeddedGaloisRestriction_commutes (B := A) j₀) hr
  let y := π (galoisUnitsRep K E) 2 z
  have hp : ContinuousCohomology.map r φ 2 y =
      π (galoisUnitsRep A M) 2 (cocyclesMap r φ 2 z) :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  calc
    restrict f (finiteInflation E y) = I (π (galoisUnitsRep A M) 2 (cocyclesMap r φ 2 z)) :=
      restrict_finiteInflation_eq_of_factor f E r j.toRingHom hr s i.toRingHom hs hgroups hcoeff z
    _ = I (ContinuousCohomology.map r φ 2 y) := congrArg (fun b => I b) hp.symm
    _ = I (ContinuousCohomology.map r₀ φ₀ 2 y) :=
      congrArg (fun b => I b) (ConcreteCategory.congr_hom hmap y)

/-- The actual absolute restriction vanishes precisely when the relative
restriction through a compatible finite completed stage vanishes. -/
theorem restrict_finiteInflation_eq_zero_iff_embeddedRelativeRestriction (e : A ≃ₐ[K] B)
    (j₀ : E →ₐ[K] M) (x : relativeBr E) :
    restrict (algebraMap K B) (finiteInflation E x) = 0 ↔
      embeddedRelativeRestriction (A := A) E j₀ x = 0 := by
  rw [restrict_finiteInflation_eq_embeddedRelativeRestriction E e j₀ x]
  exact ⟨fun h => embeddedRelativeToAbsolute_injective (M := M) e
    (h.trans (map_zero (embeddedRelativeToAbsolute (M := M) e)).symm),
    fun h => by rw [h, map_zero]⟩

end RestrictFromGlobal

/-- A finite-stage restriction along a specified embedding into the target
separable closure inflates to the canonical absolute restriction. -/
theorem restrict_finiteInflation_eq_finiteInflation_embeddedRelativeRestriction
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (M : FiniteGaloisIntermediateField F (SeparableClosure F))
    [Algebra K M] [IsScalarTower K F M] (j₀ : E →ₐ[K] M) (x : relativeBr E) :
    restrict (algebraMap K F) (finiteInflation E x) =
      finiteInflation M (embeddedRelativeRestriction E j₀ x) := by
  let f := algebraMap K F
  let Ω := SeparableClosure F
  let : Algebra K Ω := ((algebraMap F Ω).comp f).toAlgebra
  let i := M.toIntermediateField.val.toRingHom
  let b₀ : E →ₐ[K] Ω :=
    { __ := (Field.absoluteGaloisGroup.separableClosureLift f).comp
        E.toIntermediateField.val.toRingHom
      commutes' := fun a => Field.absoluteGaloisGroup.separableClosureLift_algebraMap f a }
  let b : E →ₐ[K] Ω :=
    { __ := i.comp j₀.toRingHom
      commutes' := fun a => by
        change i (j₀ (algebraMap K E a)) = algebraMap F Ω (f a)
        rw [j₀.commutes, IsScalarTower.algebraMap_apply K F M]
        rfl }
  obtain ⟨τ, hτ⟩ := ClassFieldTheory.exists_embedding_comp_aut_eq_of_normal b₀ b
  let j := j₀.comp τ.toAlgHom
  have hcoeff (a : E) : i (j a) = Field.absoluteGaloisGroup.separableClosureLift f a := hτ a
  let r := embeddedGaloisRestriction (B := F) j
  let r₀ := embeddedGaloisRestriction (B := F) j₀
  let s := finiteGaloisRestriction M
  let hr := embeddedGaloisRestriction_commutes (B := F) j
  let hr₀ := embeddedGaloisRestriction_commutes (B := F) j₀
  let hs := finiteGaloisRestriction_commutes M
  have hgroups (σ : Gal(Ω/F)) :
      r (s σ) = finiteGaloisRestriction E (Field.absoluteGaloisGroup.separableMap f σ) := by
    apply AlgEquiv.ext
    intro a
    apply E.toIntermediateField.val.injective
    apply (Field.absoluteGaloisGroup.separableClosureLift f).injective
    change Field.absoluteGaloisGroup.separableClosureLift f (r (s σ) a) =
      Field.absoluteGaloisGroup.separableClosureLift f
        (finiteGaloisRestriction E (Field.absoluteGaloisGroup.separableMap f σ) a)
    have hleft : Field.absoluteGaloisGroup.separableClosureLift f (r (s σ) a) =
        σ (Field.absoluteGaloisGroup.separableClosureLift f (a : SeparableClosure K)) :=
      (hcoeff (r (s σ) a)).symm.trans ((congrArg i (hr (s σ) a)).trans
        ((hs σ (j a)).trans (congrArg σ (hcoeff a))))
    have hright := (congrArg (Field.absoluteGaloisGroup.separableClosureLift f)
      (finiteGaloisRestriction_commutes E (Field.absoluteGaloisGroup.separableMap f σ) a)).trans
      (Field.absoluteGaloisGroup.separableMap_commutes f σ (a : SeparableClosure K))
    exact hleft.trans hright.symm
  let φ := galoisUnitsMap r j.toRingHom hr
  let φ₀ := galoisUnitsMap r₀ j₀.toRingHom hr₀
  have hmap : ContinuousCohomology.map r φ 2 = ContinuousCohomology.map r₀ φ₀ 2 :=
    relativeCohomologyMap_comp_aut τ j₀.toRingHom r₀ r hr₀ hr
  obtain ⟨z, rfl⟩ := π_surjective (galoisUnitsRep K E) 2 x
  let y := π (galoisUnitsRep K E) 2 z
  have hp : ContinuousCohomology.map r φ 2 y =
      π (galoisUnitsRep F M) 2 (cocyclesMap r φ 2 z) :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  calc
    restrict f (finiteInflation E y) =
        finiteInflation M (π (galoisUnitsRep F M) 2 (cocyclesMap r φ 2 z)) :=
      restrict_finiteInflation_eq_of_factor f E r j.toRingHom hr s i hs hgroups hcoeff z
    _ = finiteInflation M (ContinuousCohomology.map r φ 2 y) := congrArg (finiteInflation M) hp.symm
    _ = finiteInflation M (ContinuousCohomology.map r₀ φ₀ 2 y) :=
      congrArg (finiteInflation M) (ConcreteCategory.congr_hom hmap y)

end ClassFieldTheory.Brauer
