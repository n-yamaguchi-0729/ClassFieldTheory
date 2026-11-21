/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Irreducible
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.InducedCoefficientEuler

/-! # Reduction of the local Euler formula to irreducible finite-stage coefficients -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)

private theorem exists_monoidHom_lift
    {J Q M : Type u} [Group J] [Group Q] [Monoid M]
    (f : J →* Q) (hf : Function.Surjective f) (a : J →* M) (h : f.ker ≤ a.ker) :
    ∃ b : Q →* M, ∀ x : J, b (f x) = a x := by
  let u : J →* Mˣ := a.toHomUnits
  have hu : f.ker ≤ u.ker := by
    intro x hx
    change u x = 1
    apply Units.ext
    exact h hx
  let v : Q →* Mˣ := f.liftOfSurjective hf ⟨u, hu⟩
  refine ⟨(Units.coeHom M).comp v, fun x => ?_⟩
  have hx : v (f x) = u x := MonoidHom.liftOfRightInverse_comp_apply (f := f)
    (f_inv := Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨u, hu⟩ x
  exact congrArg Units.val hx

/-- A continuous prime-annihilated coefficient action factors through an
actual finite Galois stage on the original coefficient group. -/
theorem exists_finiteStagePrimeCoefficient (p : ℕ) [Fact p.Prime]
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0) :
    letI : Module (ZMod p) A := AddCommGroup.zmodModule hp
    ∃ E : FiniteGaloisIntermediateField K Ω, ∃ ρ : Representation (ZMod p) Gal(E/K) A,
      Nonempty (finiteStageIntegralCoefficient K E ρ ≅ A) := by
  let : Module ℤ A := A.hV2
  let : Module (ZMod p) A := AddCommGroup.zmodModule hp
  let endMonoid : Monoid (Module.End (ZMod p) A) := Module.End.instMonoid
  let : Monoid (Module.End (ZMod p) A) := endMonoid
  let ρ : Representation (ZMod p) G A := Representation.overZMod p A.ρ.toRepresentation
  let N := @MonoidHom.ker G _ (Module.End (ZMod p) A) endMonoid.toMulOneClass ρ
  have hk : (N : Set G) = ⋂ a : A, (fun g => A.ρ g a) ⁻¹' {a} := by
    ext g
    rw [Set.mem_iInter]
    change ρ g = endMonoid.one ↔ ∀ a, A.ρ g a = a
    exact ⟨fun h a => congrArg (fun f : A →ₗ[ZMod p] A => f.toFun a) h,
      fun h => LinearMap.ext h⟩
  have ho : IsOpen (N : Set G) := by
    rw [hk]
    exact isOpen_iInter_of_finite fun a => (isOpen_discrete {a}).preimage
      (hA.comp (continuous_id.prodMk continuous_const))
  obtain ⟨E, hE⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
    (k := K) (K := Ω) (N : Set G)).mp (ho.mem_nhds (Subgroup.one_mem _))
  let r := (finiteGaloisRestriction E).toMonoidHom
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  have hker : r.ker ≤ N := by
    change (AlgEquiv.restrictNormalHom E.toIntermediateField).ker ≤ N
    rw [IntermediateField.restrictNormalHom_ker]
    exact hE
  obtain ⟨ρE, he⟩ := @exists_monoidHom_lift G Gal(E/K) (Module.End (ZMod p) A)
    _ _ endMonoid r hr ρ hker
  refine ⟨E, ρE, ⟨discreteIntegralCoefficientIso (AddEquiv.refl A) ?_⟩⟩
  intro g a
  change (ρE (r g)).toFun a = A.ρ g a
  exact congrArg (fun f : A →ₗ[ZMod p] A => f.toFun a) (he g)

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] in
/-- The restricted action at a finite stage is jointly continuous with its
actual discrete coefficients. -/
theorem finiteStageIntegralCoefficient_actionContinuous
    (E : FiniteGaloisIntermediateField K Ω) (k : Type*) [Field k]
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k Gal(E/K) V) :
    let C := finiteStageIntegralCoefficient K E ρ
    Continuous (fun gv : G × C => C.ρ gv.1 gv.2) := by
  intro C
  let f (qv : Gal(E/K) × C) : C := ρ (qv.1 : Gal(E/K)) (qv.2 : V)
  exact (continuous_of_discreteTopology (f := f)).comp
    ((finiteGaloisRestriction E).continuous.prodMap continuous_id)

private theorem finiteStageEuler_of_subrepresentation
    (E : FiniteGaloisIntermediateField K Ω) (k : Type*) [Field k] [Finite k]
    {V : Type u} [AddCommGroup V] [Module k V] [Finite V]
    (ρ : Representation k Gal(E/K) V) (W : Subrepresentation ρ)
    (hW : hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E W.toRepresentation))
    (hQ : hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E W.quotient)) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E ρ) := by
  let X := (finiteStageIntegralCoefficient K E W.toRepresentation)
  let Y := (finiteStageIntegralCoefficient K E ρ)
  let J := (finiteStageIntegralCoefficient K E W.quotient)
  let f : X ⟶ Y := ConcreteCategory.ofHom
    { toLinearMap := (W.toSubmodule.subtype.toAddMonoidHom).toIntLinearMap
      cont := continuous_of_discreteTopology
      isIntertwining' := fun _ => ContinuousLinearMap.ext fun _ => rfl }
  let R := coefficientRangeShortComplex ℤ G X Y f
  have h' : LinearMap.range f.hom.toContinuousLinearMap.toLinearMap =
      W.toSubmodule.restrictScalars ℤ := by
    ext x
    refine ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rintro ⟨a, ha⟩
    let a₀ : W.toSubmodule := a
    change (a₀ : V) = x at ha
    exact ha ▸ a₀.property
  let : Module ℤ Y := Y.hV2
  let : Module ℤ J := J.hV2
  let s := LinearMap.range f.hom.toContinuousLinearMap.toLinearMap
  let q : Y →ₗ[ℤ] J := W.toSubmodule.mkQ.toAddMonoidHom.toIntLinearMap
  have hq : Function.Surjective q := Submodule.mkQ_surjective W.toSubmodule
  have hqk : q.ker = W.toSubmodule.restrictScalars ℤ := by
    ext y
    let y₀ : V := y
    change (Submodule.Quotient.mk (p := W.toSubmodule) y₀ : V ⧸ W.toSubmodule) = 0 ↔
      y₀ ∈ W.toSubmodule
    exact Submodule.Quotient.mk_eq_zero (p := W.toSubmodule) (x := y₀)
  have hker : s = q.ker := h'.trans hqk.symm
  let e : R.X₃ ≃+ J :=
    ((Submodule.quotEquivOfEq s q.ker hker).trans (q.quotKerEquivOfSurjective hq)).toAddEquiv
  have heq (y : Y) : e (R.g y) = q y := by
    change (q.quotKerEquivOfSurjective hq)
      (Submodule.quotEquivOfEq s q.ker hker (Submodule.Quotient.mk y)) = q y
    rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have he (g : G) (x : R.X₃) : e (R.X₃.ρ g x) = J.ρ g (e x) := by
    have hsurj : Function.Surjective R.g :=
      invariantCoefficientQuotientProjection_surjective ℤ G Y s
        (coefficientMapRange_invariant ℤ G X Y f)
    obtain ⟨y, rfl⟩ := hsurj x
    have hg : q (Y.ρ g y) = J.ρ g (q y) := rfl
    exact (congrArg e (R.g.hom.isIntertwining g y).symm).trans
      ((heq (Y.ρ g y)).trans (hg.trans (congrArg (J.ρ g) (heq y).symm)))
  let : Finite X := inferInstanceAs (Finite ↥W.toSubmodule)
  let : Finite Y := inferInstanceAs (Finite V)
  let : DiscreteTopology R.X₃ := invariantCoefficientQuotient_discrete ℤ G Y s
    (coefficientMapRange_invariant ℤ G X Y f)
  exact hasLowDegreeEulerCharacteristic_of_range G (localCoefficientOrderNorm K)
    (localCoefficientOrderNorm_mul K) (finiteLocalIntegralH3_isZero K) X Y f Subtype.val_injective
    (finiteStageIntegralCoefficient_actionContinuous K E k W.toRepresentation)
    (finiteStageIntegralCoefficient_actionContinuous K E k ρ) hW
    (hasLowDegreeEulerCharacteristic_of_iso (discreteIntegralCoefficientIso e he).symm hQ)

/-- Exactness on the actual subrepresentation and quotient extends the Euler
formula from irreducible representations over a finite coefficient field. -/
theorem finiteStageEuler_of_irreducible
    (E : FiniteGaloisIntermediateField K Ω) (k : Type*) [Field k] [Finite k]
    (hSimple : ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [Nontrivial V] (ρ : Representation k Gal(E/K) V), Representation.IsIrreducible ρ →
        hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E ρ))
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Gal(E/K) V) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E ρ) := by
  let P (n : ℕ) := ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    Module.finrank k V = n → ∀ ρ : Representation k Gal(E/K) V,
      hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E ρ)
  have hP (n : ℕ) : P n := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro V _ _ _ hn ρ
      cases subsingleton_or_nontrivial V with
      | inl h =>
        let : Subsingleton (finiteStageIntegralCoefficient K E ρ) := h
        exact hasLowDegreeEulerCharacteristic_of_subsingleton G (localCoefficientOrderNorm K)
          (localCoefficientOrderNorm_one K) (finiteStageIntegralCoefficient K E ρ)
      | inr h =>
        by_cases hρ : Representation.IsIrreducible ρ
        · exact hSimple V ρ hρ
        change ¬ IsSimpleOrder (Subrepresentation ρ) at hρ
        rw [isSimpleOrder_iff_isAtom_top] at hρ
        have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun hh =>
          bot_ne_top (congrArg Subrepresentation.toSubmodule hh)
        obtain ⟨W, hW₁, hW₂⟩ : ∃ W : Subrepresentation ρ, W < ⊤ ∧ W ≠ ⊥ := by
          by_contra! hW
          exact hρ ⟨hbt.symm, hW⟩
        have hWlt : W.toSubmodule < ⊤ := lt_top_iff_ne_top.mpr
          (fun he => hW₁.ne (Subrepresentation.toSubmodule_injective he))
        have hWne : W.toSubmodule ≠ ⊥ := fun he => hW₂ (Subrepresentation.toSubmodule_injective he)
        have hlt : Module.finrank k W.toSubmodule < n := by
          rw [← hn, ← finrank_top k V]
          exact Submodule.finrank_lt_finrank_of_lt hWlt
        have hpos : 0 < Module.finrank k W.toSubmodule := by
          exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hWne)
        have hqlt : Module.finrank k (V ⧸ W.toSubmodule) < n := by
          have := W.toSubmodule.finrank_quotient_add_finrank
          omega
        let b := Module.finBasis k V
        let : Finite V := Finite.of_injective b.equivFun b.equivFun.injective
        exact finiteStageEuler_of_subrepresentation K E k ρ W
          (ih _ hlt W.toSubmodule rfl W.toRepresentation)
          (ih _ hqlt (V ⧸ W.toSubmodule) rfl W.quotient)
  exact hP _ V rfl ρ

end ClassFieldTheory.Brauer
