/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.AlexandrovDiscrete
public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness
public import Nyll.GaloisCohomology.Topology.DiscreteGroupH2

/-! # Continuous and ordinary cohomology of discrete groups -/

public section

open CategoryTheory TopRep
open scoped BigOperators

noncomputable section

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
    (X : TopRep.{u} ℤ G)

private def consecutiveIncrements (n : ℕ) (a : Fin (n + 1) → G) : Fin n → G :=
  fun i => (a i.castSucc)⁻¹ * a i.succ

private def homogeneousTupleOfInhomogeneous (n : ℕ) (f : (Fin n → G) → X) : C(Fin (n + 1) → G, X) :=
  ⟨fun a => X.ρ (a 0) (f (consecutiveIncrements n a)), continuous_of_discreteTopology⟩

omit [IsTopologicalGroup G] in
private theorem homogeneousTupleOfInhomogeneous_equivariant (n : ℕ) (f : (Fin n → G) → X)
    (g : G) (a : Fin (n + 1) → G) :
    homogeneousTupleOfInhomogeneous X n f (fun i => g * a i) =
      X.ρ g (homogeneousTupleOfInhomogeneous X n f a) := by
  have h : consecutiveIncrements n (fun i => g * a i) = consecutiveIncrements n a := by
    funext i
    simp only [consecutiveIncrements, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  change X.ρ (g * a 0) (f (consecutiveIncrements n (fun i => g * a i))) =
    X.ρ g (X.ρ (a 0) (f (consecutiveIncrements n a)))
  rw [h]
  exact DFunLike.congr_fun (map_mul X.ρ g (a 0)) (f (consecutiveIncrements n a))

/-- Homogeneous normalized evaluation on a discrete group, with its original coefficients. -/
def homogeneousEvaluationEquiv (n : ℕ) :
    ((continuousModuleComplexFunctor G).obj X).X n ≃ₗ[ℤ]
      ((IntegralGroupCohomology.integerScalars.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (groupCohomology.inhomogeneousCochains (underlyingIntegralRep X))).X n := by
  refine AddEquiv.toIntLinearEquiv
    {
      toFun z a := resolutionTupleHomeomorph G X (n + 1) z.val (Fin.partialProd a)
      invFun f := homogeneousCochainOfTuple G X n (homogeneousTupleOfInhomogeneous X n f)
        (homogeneousTupleOfInhomogeneous_equivariant X n f)
      left_inv z := by
        apply Subtype.ext
        apply (resolutionTupleHomeomorph G X (n + 1)).injective
        apply ContinuousMap.ext
        intro a
        rw [homogeneousCochainOfTuple_apply]
        change X.ρ (a 0) (resolutionTupleHomeomorph G X (n + 1) z.val
          (Fin.partialProd (consecutiveIncrements n a))) =
          resolutionTupleHomeomorph G X (n + 1) z.val a
        have h : (fun i => a 0 * Fin.partialProd (consecutiveIncrements n a) i) = a :=
          Fin.partialProd_left_inv a
        exact (homogeneousCochain_tuple_equivariant G X n z (a 0)
          (Fin.partialProd (consecutiveIncrements n a))).symm.trans
            (congrArg (resolutionTupleHomeomorph G X (n + 1) z.val) h)
      right_inv f := by
        funext a
        change resolutionTupleHomeomorph G X (n + 1)
          (homogeneousCochainOfTuple G X n (homogeneousTupleOfInhomogeneous X n f)
            (homogeneousTupleOfInhomogeneous_equivariant X n f)).val (Fin.partialProd a) = f a
        rw [homogeneousCochainOfTuple_apply]
        have h : consecutiveIncrements n (Fin.partialProd a) = a :=
          funext (Fin.partialProd_right_inv a)
        change X.ρ (Fin.partialProd a 0) (f (consecutiveIncrements n (Fin.partialProd a))) = f a
        rw [h, Fin.partialProd_zero, map_one]
        rfl
      map_add' z w := by
        funext a
        change resolutionTupleHomeomorph G X (n + 1) (z.val + w.val) (Fin.partialProd a) = _
        rw [resolutionTupleHomeomorph_add, ContinuousMap.add_apply]
        rfl
    }

/-- Evaluation intertwines the continuous and ordinary integral cochain differentials. -/
def discreteIntegralCochainIso :
    (continuousModuleComplexFunctor G).obj X ≅
      (IntegralGroupCohomology.integerScalars.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (groupCohomology.inhomogeneousCochains (underlyingIntegralRep X)) := by
  let D := groupCohomology.inhomogeneousCochains (underlyingIntegralRep X)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (homogeneousEvaluationEquiv X n).toModuleIso) ?_
  intro n m hn
  change n + 1 = m at hn
  subst m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext a
  symm
  change resolutionTupleHomeomorph G X (n + 2)
    (((homogeneousCochains X).d n (n + 1)) z).val (Fin.partialProd a) =
    ((D.d n (n + 1)) (fun b => resolutionTupleHomeomorph G X (n + 1) z.val (Fin.partialProd b))) a
  rw [homogeneousCochains.d_eq]
  change resolutionTupleHomeomorph G X (n + 2)
    ((TopRep.d X (n + 1)).hom z.val) (Fin.partialProd a) =
    ((D.d n (n + 1)) (fun b => resolutionTupleHomeomorph G X (n + 1) z.val (Fin.partialProd b))) a
  rw [resolutionTupleHomeomorph_d, groupCohomology.inhomogeneousCochains.d_def]
  let smul₀ (r : ULift.{u} ℤ) (x : underlyingIntegralRep X) : underlyingIntegralRep X :=
    @SMul.smul (ULift.{u} ℤ) (underlyingIntegralRep X)
      (underlyingIntegralRep X).hV2.toDistribMulAction.toDistribSMul.toSMul r x
  let f : (Fin n → G) → underlyingIntegralRep X :=
    fun b => resolutionTupleHomeomorph G X (n + 1) z.val (Fin.partialProd b)
  have hd := inhomogeneousCochains.d_hom_apply (underlyingIntegralRep X) n f a
  refine Eq.trans ?_ hd.symm
  have hρ : (underlyingIntegralRep X).ρ (a 0) (f (Fin.tail a)) =
      X.ρ (a 0) (f (Fin.tail a)) := rfl
  have hterm (j : Fin (n + 1)) :
      smul₀ ((-1 : ULift.{u} ℤ) ^ ((j : ℕ) + 1)) (f (Fin.contractNth j (· * ·) a)) =
        (-1 : ℤ) ^ ((j : ℕ) + 1) • (show X from f (Fin.contractNth j (· * ·) a)) := by
    have hp := (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).map_pow (-1) ((j : ℕ) + 1)
    let y : X := f (Fin.contractNth j (· * ·) a)
    have hs : smul₀ ((-1 : ULift.{u} ℤ) ^ ((j : ℕ) + 1)) y =
        X.hV2.smul (((-1 : ULift.{u} ℤ) ^ ((j : ℕ) + 1)).down) y := rfl
    exact hs.trans ((congrArg (fun r => X.hV2.smul r y) hp).trans (int_smul_eq_zsmul X.hV2 _ y))
  have hsum : (∑ j : Fin (n + 1), smul₀ ((-1 : ULift.{u} ℤ) ^ ((j : ℕ) + 1))
      (f (Fin.contractNth j (· * ·) a))) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
        (show X from f (Fin.contractNth j (· * ·) a)) :=
    Finset.sum_congr rfl fun j _ => hterm j
  have hrs := congrArg₂ (fun y z : underlyingIntegralRep X => y + z) hρ hsum
  refine Eq.trans ?_ hrs.symm
  change _ = X.ρ (a 0)
    (resolutionTupleHomeomorph G X (n + 1) z.val (Fin.partialProd (Fin.tail a))) +
    ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
      resolutionTupleHomeomorph G X (n + 1) z.val (Fin.partialProd (Fin.contractNth j (· * ·) a))
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, one_smul, Fin.zero_succAbove]
  congr 1
  · have h : (fun j => Fin.partialProd a j.succ) =
        fun j => a 0 * Fin.partialProd (Fin.tail a) j := funext (Fin.partialProd_succ' a)
    rw [h]
    exact homogeneousCochain_tuple_equivariant G X n z (a 0) (Fin.partialProd (Fin.tail a))
  · apply Finset.sum_congr rfl
    intro j _
    rw [Fin.partialProd_contractNth]
    rfl

/-- For a discrete acting group the original continuous cohomology agrees
with ordinary group cohomology on the same coefficients, in every degree. -/
def discreteIntegralCohomologyEquiv (n : ℕ) :
    continuousCohomology n X ≃+ groupCohomology (underlyingIntegralRep X) n := by
  let D := groupCohomology.inhomogeneousCochains (underlyingIntegralRep X)
  let e := (continuousModuleHomologyIso G X n).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) n).mapIso
      (discreteIntegralCochainIso X) ≪≫ (D.sc n).mapHomologyIso
        IntegralGroupCohomology.integerScalars
  exact AddEquiv.ofBijective e.hom.hom.toAddMonoidHom (ConcreteCategory.bijective_of_isIso e.hom)

end ContinuousCohomology
