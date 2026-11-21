/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.GaloisCohomology.Topology.ContinuousRepresentationUniverseLift
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RightQuotient

/-! # Actual continuous coinduction along an open subgroup -/

@[expose] public section

open CategoryTheory ContRepresentation ReidemeisterSchreier.Profinite
open scoped Topology

noncomputable section

namespace TopRep

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G)

variable (A : TopRep.{u} ℤ (↥U.toSubgroup))

/-- The actual coinduced representation consists of left-equivariant continuous maps. -/
def openCoinduced (A : TopRep.{u} ℤ (↥U.toSubgroup)) : TopRep.{u} ℤ G := by
  let i : ↥U.toSubgroup →ₜ* G := ProCGroups.ContinuousMonoidHom.subtype U.toSubgroup
  let : Module ℤ A := A.hV2
  let ρ : ContRepresentation ℤ (↥U.toSubgroup) A := A.ρ
  let X := ContRepresentation.coindV i ρ
  let : Module ℤ X := X.module
  exact TopRep.of (X := X) (ContRepresentation.coind i ρ)

include A

attribute [local instance] TopRep.integralModuleOfRepresentation

/-- Point evaluation is a continuous integral-linear map on the coinduced carrier. -/
def openCoinducedValue (g : G) : openCoinduced U A →L[ℤ] A where
  toFun := fun f => f.val g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_eval_const g).comp continuous_subtype_val

/-- Evaluation at the identity is the subgroup map of continuous coinduction. -/
def openCoinducedEval : TopRep.res U.toSubgroup.subtype (openCoinduced U A) ⟶ A := by
  let X := TopRep.res U.toSubgroup.subtype (openCoinduced U A)
  let ev : X →L[ℤ] A := openCoinducedValue U A 1
  let m : ContIntertwiningMap X.ρ A.ρ :=
    { toContinuousLinearMap := ev
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro f
        change f.val (1 * (g : G)) = A.ρ g (f.val 1)
        exact (congrArg f.val (one_mul (g : G))).trans
          ((congrArg f.val (mul_one (g : G))).symm.trans (f.property g 1)) }
  exact ConcreteCategory.ofHom (C := TopRep ℤ (↥U.toSubgroup)) m

theorem openCoinducedEval_apply (f : openCoinduced U A) : openCoinducedEval U A f = f.val 1 := rfl

variable (hA : Continuous (fun ga : (↥U.toSubgroup) × (A : Type u) => A.ρ ga.1 ga.2))

include hA

/-- The actual coinduced coefficient is determined by its values at the finite cosets. -/
def openCoinducedCoordinates :
    openCoinduced U A ≃ (OpenSubgroupRightQuotient U → A) := by
  let q : G → (OpenSubgroupRightQuotient U) := openSubgroupRightCoset U
  let s : (OpenSubgroupRightQuotient U) → G := openSubgroupRightCosetSection U
  let r := openSubgroupRetraction U
  have hq : Continuous q := isQuotientMap_quotient_mk'.continuous
  have hs (x : OpenSubgroupRightQuotient U) : q (s x) = x :=
    openSubgroupRightCosetSection_spec U x
  have hprod (g : G) : (r g : G) * s (q g) = g := by
    change (g * (s (q g))⁻¹) * s (q g) = g
    exact inv_mul_cancel_right g (s (q g))
  have hret (x : (OpenSubgroupRightQuotient U)) : r (s x) = 1 := by
    apply Subtype.ext
    change s x * (s (q (s x)))⁻¹ = 1
    rw [hs, mul_inv_cancel]
  let F (b : (OpenSubgroupRightQuotient U) → A) : C(G, A) := ⟨fun g => A.ρ (r g) (b (q g)),
    hA.comp (r.continuous.prodMk ((continuous_of_discreteTopology (f := b)).comp hq))⟩
  have hF (b : (OpenSubgroupRightQuotient U) → A) (h : U.toSubgroup) (g : G) :
      F b ((h : G) * g) = A.ρ h (F b g) := by
    change A.ρ (r ((h : G) * g)) (b (q ((h : G) * g))) = A.ρ h (A.ρ (r g) (b (q g)))
    have hr : r ((h : G) * g) = h * r g := openSubgroupRetraction_subgroup_mul U h g
    have hqg : q ((h : G) * g) = q g := openSubgroupRightCoset_subgroup_mul U h g
    rw [hr, hqg]
    exact congrArg (fun f : A →L[ℤ] A => f (b (q g))) (map_mul A.ρ h (r g))
  refine
    { toFun := fun f x => f.val (s x)
      invFun := fun b => ⟨F b, hF b⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    change A.ρ (r g) (f.val (s (q g))) = f.val g
    exact (f.property (r g) (s (q g))).symm.trans (congrArg f.val (hprod g))
  · intro b
    funext x
    change A.ρ (r (s x)) (b (q (s x))) = b x
    rw [hret, hs]
    exact congrArg (fun f : A →L[ℤ] A => f (b x)) (map_one A.ρ)

variable [CompactSpace G]

theorem openCoinduced_finite [Finite A] : Finite (openCoinduced U A) := by
  let e : openCoinduced U A ≃ (OpenSubgroupRightQuotient U → A) :=
    openCoinducedCoordinates U A hA
  exact Finite.of_equiv ((OpenSubgroupRightQuotient U) → A) e.symm

/-- The finite coinduced coefficient has one copy of the original carrier per coset. -/
theorem natCard_openCoinduced [Finite A] :
    Nat.card (openCoinduced U A) = Nat.card A ^ U.toSubgroup.index := by
  let e : (OpenSubgroupRightQuotient U) ≃ G ⧸ U.toSubgroup :=
    QuotientGroup.quotientRightRelEquivQuotientLeftRel U.toSubgroup
  calc
    Nat.card (openCoinduced U A) = Nat.card (OpenSubgroupRightQuotient U → A) :=
      Nat.card_congr (openCoinducedCoordinates U A hA)
    _ = Nat.card A ^ Nat.card (OpenSubgroupRightQuotient U) := Nat.card_fun
    _ = Nat.card A ^ U.toSubgroup.index :=
      congrArg (Nat.card A ^ ·) ((Nat.card_congr e).trans U.toSubgroup.index_eq_card.symm)

/-- With discrete coefficients on the open subgroup, coset evaluation is a homeomorphism. -/
def openCoinducedDiscreteCoordinates [DiscreteTopology A] :
    openCoinduced U A ≃ₜ (OpenSubgroupRightQuotient U → A) := by
  let e : openCoinduced U A ≃ (OpenSubgroupRightQuotient U → A) :=
    openCoinducedCoordinates U A hA
  have hTo : Continuous e := by
    apply continuous_pi
    intro x
    change Continuous (fun f : openCoinduced U A => f.val (openSubgroupRightCosetSection U x))
    exact (continuous_eval_const (openSubgroupRightCosetSection U x)).comp continuous_subtype_val
  have hInv : Continuous e.symm := continuous_of_discreteTopology
  exact ⟨e, hTo, hInv⟩

theorem openCoinduced_discrete [DiscreteTopology A] : DiscreteTopology (openCoinduced U A) :=
  (openCoinducedDiscreteCoordinates U A hA).symm.discreteTopology

/-- The ambient action on the actual coinduced discrete coefficients is jointly continuous. -/
theorem openCoinduced_action_continuous [DiscreteTopology A] :
    Continuous (fun gf : G × openCoinduced U A => (openCoinduced U A).ρ gf.1 gf.2) := by
  let e : openCoinduced U A ≃ₜ (OpenSubgroupRightQuotient U → A) :=
    openCoinducedDiscreteCoordinates U A hA
  have hc : Continuous (fun gf : G × openCoinduced U A =>
      e ((openCoinduced U A).ρ gf.1 gf.2)) := by
    apply continuous_pi
    intro x
    have heq (gf : G × (openCoinduced U A)) : e (((openCoinduced U A)).ρ gf.1 gf.2) x =
        gf.2.val (openSubgroupRightCosetSection U x * gf.1) := by
      rcases gf with ⟨g, ⟨f, hf⟩⟩
      rfl
    exact (continuous_eval.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_const.mul continuous_fst))).congr (fun gf => (heq gf).symm)
  exact (e.symm.continuous.comp hc).congr (fun gf => e.symm_apply_apply _)

end TopRep
