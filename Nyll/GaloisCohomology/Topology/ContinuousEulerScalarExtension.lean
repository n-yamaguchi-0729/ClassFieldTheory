/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousEulerMultiplicity
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Descent of the low-degree Euler ratio along repeated coefficients -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousCohomology
open scoped BigOperators TensorProduct

noncomputable section

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {W : Type*} {M : Type*}
  [AddCommMonoid W] [Module R W] [AddCommMonoid M] [Module R M] {d : ℕ}

/-- A basis of the scalar factor identifies the underlying extended module
with one copy of the original module for each basis vector. -/
def repeatedCoefficientBasisEquiv (b : Module.Basis (Fin d) R W) :
    W ⊗[R] M ≃ₗ[R] (Fin d → M) :=
  equivFinsuppOfBasisLeft b ≪≫ₗ Finsupp.linearEquivFunOnFinite R M (Fin d)

/-- Under the basis comparison, extending an operator is the same as
applying it to each coordinate. This applies to every element of a finite stage group. -/
theorem repeatedCoefficientBasisEquiv_map (b : Module.Basis (Fin d) R W)
    (f : M →ₗ[R] M) (x : W ⊗[R] M) (i : Fin d) :
    repeatedCoefficientBasisEquiv b (TensorProduct.map LinearMap.id f x) i =
      f (repeatedCoefficientBasisEquiv b x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul w m =>
      change equivFinsuppOfBasisLeft b (TensorProduct.map LinearMap.id f (w ⊗ₜ[R] m)) i =
        f (equivFinsuppOfBasisLeft b (w ⊗ₜ[R] m) i)
      simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end TensorProduct

namespace TopRep

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual `d` repeated coefficients, with the action applied separately in each coordinate. -/
def repeatedContinuousCoefficient (d : ℕ) (A : TopRep.{u} ℤ G) : TopRep.{u} ℤ G := by
  let : Module ℤ A := A.hV2
  let : Module ℤ (Fin d → A) := Pi.module (Fin d) (fun _ => A) ℤ
  let action : G →* (Fin d → A) →L[ℤ] (Fin d → A) :=
    { toFun := fun g => ContinuousLinearMap.pi
        (fun i : Fin d => (A.ρ g).comp (ContinuousLinearMap.proj i))
      map_one' := by
        apply ContinuousLinearMap.ext
        intro a
        funext i
        exact congrArg (fun f : A →L[ℤ] A => f (a i)) (map_one A.ρ)
      map_mul' g h := by
        apply ContinuousLinearMap.ext
        intro a
        funext i
        exact congrArg (fun f : A →L[ℤ] A => f (a i)) (map_mul A.ρ g h) }
  exact TopRep.of (ContRepresentation.ofMonoidHom action)

/-- Projection and one-coordinate insertion give the usual finite biproduct diagram. -/
def repeatedContinuousCoefficientBicone (d : ℕ) (A : TopRep.{u} ℤ G) :
    Bicone (fun _ : Fin d => A) := by
  let : Module ℤ A := A.hV2
  let B := repeatedContinuousCoefficient G d A
  let : Module ℤ (Fin d → A) := B.hV2
  let : Module ℤ B := B.hV2
  let project (i : Fin d) : ContIntertwiningMap B.ρ A.ρ :=
    ⟨ContinuousLinearMap.proj i, fun _ => rfl⟩
  let inject (i : Fin d) : ContIntertwiningMap A.ρ B.ρ :=
    ⟨ContinuousLinearMap.single ℤ (fun _ : Fin d => A) i, fun g => by
      apply ContinuousLinearMap.ext
      intro a
      funext j
      change (Pi.single i (A.ρ g a) : Fin d → A) j = A.ρ g ((Pi.single i a : Fin d → A) j)
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_of_ne h, map_zero]⟩
  refine
    { pt := B
      π := fun i => ConcreteCategory.ofHom (C := TopRep ℤ G) (project i)
      ι := fun i => ConcreteCategory.ofHom (C := TopRep ℤ G) (inject i)
      ι_π := ?_ }
  intro i j
  by_cases h : i = j
  · subst j
    rw [dite_eq_left rfl, eqToHom_refl]
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := A.ρ) (π₂ := A.ρ)
    apply ContinuousLinearMap.ext
    intro a
    change (Pi.single i a : Fin d → A) i = a
    rw [Pi.single_eq_same]
  · rw [dite_eq_right h]
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := A.ρ) (π₂ := A.ρ)
    apply ContinuousLinearMap.ext
    intro a
    change (Pi.single i a : Fin d → A) j = 0
    rw [Pi.single_eq_of_ne (Ne.symm h)]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The sum of the coordinate projections followed by their inclusions is the identity. -/
theorem repeatedContinuousCoefficientBicone_total (d : ℕ) (A : TopRep.{u} ℤ G) :
    let b := repeatedContinuousCoefficientBicone G d A
    (∑ i : Fin d, b.π i ≫ b.ι i) = 𝟙 b.pt := by
  intro b
  let : Module ℤ b.pt := b.pt.hV2
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext (π₁ := b.pt.ρ) (π₂ := b.pt.ρ)
  apply ContinuousLinearMap.ext
  intro x
  let evaluate : (b.pt ⟶ b.pt) →+ b.pt :=
    { toFun := fun f => f.hom.toContinuousLinearMap x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change evaluate _ = evaluate _
  rw [map_sum]
  exact LinearMap.sum_single_apply (fun _ : Fin d => A) (show Fin d → A from x)

variable [LocallyCompactSpace G]

local notation "C" => continuousModuleComplexFunctor G

/-- Continuous cohomology of the actual repeated coefficient is the product of
the original cohomology, through the same coordinate projections. -/
def repeatedContinuousCoefficientHomologyEquiv (d : ℕ) (A : TopRep.{u} ℤ G) (j : ℕ) :
    ((C).obj (repeatedContinuousCoefficient G d A)).homology j ≃
      (Fin d → ((C).obj A).homology j) := by
  let H := (C) ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) j
  let b := repeatedContinuousCoefficientBicone G d A
  let D : Fin d → ModuleCat.{u} ℤ := fun _ => H.obj A
  let c : Bicone D := H.mapBicone b
  have htotal : (∑ i : Fin d, c.π i ≫ c.ι i) = 𝟙 c.pt := by
    change (∑ i : Fin d, H.map (b.π i) ≫ H.map (b.ι i)) = 𝟙 (H.obj b.pt)
    calc
      _ = H.map (∑ i : Fin d, b.π i ≫ b.ι i) := by
        rw [H.map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (H.map_comp (b.π i) (b.ι i)).symm
      _ = _ := (congrArg H.map (repeatedContinuousCoefficientBicone_total G d A)).trans
        (H.map_id b.pt)
  let e := biproduct.uniqueUpToIso D (isBilimitOfTotal c htotal)
  exact (e ≪≫ ModuleCat.biproductIsoPi D).toLinearEquiv.toEquiv

/-- The low-degree Euler ratio of `d` copies is the `d`-th power of the original ratio. -/
theorem repeatedContinuousCoefficient_euler (d : ℕ) (A : TopRep.{u} ℤ G) :
    lowDegreeEulerCharacteristic ((C).obj (repeatedContinuousCoefficient G d A)) =
      lowDegreeEulerCharacteristic ((C).obj A) ^ d := by
  have hcard (j : ℕ) :
      Nat.card (((C).obj (repeatedContinuousCoefficient G d A)).homology j) =
        Nat.card (((C).obj A).homology j) ^ d := by
    rw [Nat.card_congr (repeatedContinuousCoefficientHomologyEquiv G d A j),
      Nat.card_fun, Nat.card_fin]
  simp only [lowDegreeEulerCharacteristic, hcard, Nat.cast_pow, div_pow, mul_pow]

/-- A positive number of copies detects the original Euler characteristic
whenever the expected cardinal weight is nonnegative and multiplicative. -/
theorem hasLowDegreeEulerCharacteristic_of_repeated
    (w : ℕ → ℚ) (hone : w 1 = 1)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → w (m * n) = w m * w n)
    (hw : ∀ m : ℕ, 0 < m → 0 ≤ w m)
    (d : ℕ) (hd : 0 < d) (A : TopRep.{u} ℤ G) [Finite A]
    (h : hasLowDegreeEulerCharacteristic G w (repeatedContinuousCoefficient G d A)) :
    hasLowDegreeEulerCharacteristic G w A := by
  have hc : Nat.card (repeatedContinuousCoefficient G d A) = Nat.card A ^ d := by
    change Nat.card (Fin d → A) = _
    rw [Nat.card_fun, Nat.card_fin]
  have hA : 0 < Nat.card A := Nat.card_pos
  have hweight (k : ℕ) : w (Nat.card A ^ k) = w (Nat.card A) ^ k := by
    induction k with
    | zero => simpa only [pow_zero] using hone
    | succ k hk =>
        rw [pow_succ, pow_succ, hmul _ _ (pow_pos hA k) hA, hk]
  refine ⟨fun j hj => ?_, ?_⟩
  · let e := repeatedContinuousCoefficientHomologyEquiv G d A j
    let : Finite (((C).obj (repeatedContinuousCoefficient G d A)).homology j) := h.1 j hj
    let : Finite (Fin d → ((C).obj A).homology j) := Finite.of_equiv _ e
    exact Finite.of_injective (fun x (_ : Fin d) => x)
      (fun _ _ hxy => congrFun hxy ⟨0, hd⟩)
  · have hh := h.2
    rw [repeatedContinuousCoefficient_euler G d A, hc, hweight] at hh
    have hnonneg : 0 ≤ lowDegreeEulerCharacteristic ((C).obj A) := by
      unfold lowDegreeEulerCharacteristic
      positivity
    exact (pow_left_inj₀ hnonneg (hw _ hA) hd.ne').mp hh

end TopRep
