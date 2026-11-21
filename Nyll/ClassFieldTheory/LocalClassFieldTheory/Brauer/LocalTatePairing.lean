/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerTrace
public import Nyll.GaloisCohomology.Topology.ContinuousCupLow
public import Nyll.GaloisCohomology.Topology.ContinuousDual

/-!
# Local Tate pairings on the original continuous cohomology

The target uses the same Kummer coefficient as the Brauer trace.
Evaluation supplies the cup product with the natural twisted dual.
-/

@[expose] public section

open CategoryTheory ContinuousCohomology LocalFieldTheory TopRep
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

/-- The absolute Krull Galois group is locally compact, by compactness and separation. -/
theorem separableAbsoluteGalois_locallyCompact (F : Type u) [Field F] :
    LocallyCompactSpace Gal(SeparableClosure F/F) := by
  let hausdorff : T2Space Gal(SeparableClosure F/F) := krullTopology_t2
  let : R1Space Gal(SeparableClosure F/F) := @T2Space.r1Space _ _ hausdorff
  let : CompactSpace Gal(SeparableClosure F/F) :=
    (InfiniteGalois.continuousMulEquivToLimit F (SeparableClosure F)).symm.compactSpace
  let : WeaklyLocallyCompactSpace Gal(SeparableClosure F/F) :=
    ⟨fun _ => ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  exact WeaklyLocallyCompactSpace.locallyCompactSpace

attribute [local instance] separableAbsoluteGalois_locallyCompact

section IntegralEvaluation

variable {Γ : Type u} [Group Γ] (X Y : TopRep.{u} ℤ Γ)

/-- Evaluation on the original dual with the integer module structures
used by continuous cup products. -/
def discreteLinearDualIntEvaluation : X →ₗ[ℤ] discreteLinearDual X Y →ₗ[ℤ] Y := by
  let f := discreteLinearDualEvaluation X Y
  let a : X →+ (discreteLinearDual X Y →ₗ[ℤ] Y) :=
    { toFun := fun x => (f x).toAddMonoidHom.toIntLinearMap
      map_zero' := LinearMap.ext fun l => DFunLike.congr_fun (map_zero f) l
      map_add' := fun x x' => LinearMap.ext fun l => DFunLike.congr_fun (map_add f x x') l }
  exact a.toIntLinearMap

/-- The canonical integral linear map evaluates the original dual. -/
theorem discreteLinearDualIntEvaluation_apply (x : X) (l : discreteLinearDual X Y) :
    discreteLinearDualIntEvaluation X Y x l = discreteLinearDualMap X Y l x := rfl

theorem discreteLinearDualIntEvaluation_continuous [DiscreteTopology X] :
    Continuous
      (fun z : X × discreteLinearDual X Y => discreteLinearDualIntEvaluation X Y z.1 z.2) :=
  discreteLinearDualEvaluation_continuous X Y

theorem discreteLinearDualIntEvaluation_equivariant (g : Γ) (x : X) (l : discreteLinearDual X Y) :
    discreteLinearDualIntEvaluation X Y (X.ρ g x) ((discreteLinearDual X Y).ρ g l) =
      Y.ρ g (discreteLinearDualIntEvaluation X Y x l) :=
  discreteLinearDualEvaluation_equivariant X Y g x l

end IntegralEvaluation

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+)
variable (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [DiscreteTopology A]

local notation "GaloisGroup" => Gal(SeparableClosure K/K)
local notation "Cohom" => _root_.continuousCohomology (k := ℤ) (G := GaloisGroup)
local notation "Mu" => separableMuTopRep K n
local notation "D" => discreteLinearDual (R := ℤ) (G := GaloisGroup) A Mu
local notation "ev" => discreteLinearDualIntEvaluation (Γ := GaloisGroup) A Mu

/-- Local cup and arithmetic trace in degrees one and one. -/
def localTatePairingOne (hn : ((n : ℕ) : K) ≠ 0)
    (x : Cohom 1 A) (y : Cohom 1 D) : ZMod (n : ℕ) :=
  localKummerTrace K n hn
    (cupOneOne (G := GaloisGroup) (A := A) (B := D) (C := Mu) ev
      (discreteLinearDualIntEvaluation_continuous A Mu)
      (discreteLinearDualIntEvaluation_equivariant A Mu) x y)

/-- The two degree-one arguments are additive in the actual pairing. -/
theorem localTatePairingOne_add_left (hn : ((n : ℕ) : K) ≠ 0)
    (x x' : Cohom 1 A) (y : Cohom 1 D) :
    localTatePairingOne K n A hn (x + x') y =
      localTatePairingOne K n A hn x y + localTatePairingOne K n A hn x' y := by
  unfold localTatePairingOne
  rw [cupOneOne_add_left, map_add]

theorem localTatePairingOne_add_right (hn : ((n : ℕ) : K) ≠ 0)
    (x : Cohom 1 A) (y y' : Cohom 1 D) :
    localTatePairingOne K n A hn x (y + y') =
      localTatePairingOne K n A hn x y + localTatePairingOne K n A hn x y' := by
  unfold localTatePairingOne
  rw [cupOneOne_add_right, map_add]

/-- Local cup and arithmetic trace with an invariant left coefficient. -/
def localTatePairingZero (hn : ((n : ℕ) : K) ≠ 0)
    (x : Cohom 0 A) (y : Cohom 2 D) : ZMod (n : ℕ) :=
  localKummerTrace K n hn
    (cupZeroTwo (G := GaloisGroup) (A := A) (B := D) (C := Mu) ev
      (discreteLinearDualIntEvaluation_continuous A Mu)
      (discreteLinearDualIntEvaluation_equivariant A Mu) x y)

/-- Local cup and arithmetic trace with an invariant dual coefficient. -/
def localTatePairingTwo (hn : ((n : ℕ) : K) ≠ 0)
    (x : Cohom 2 A) (y : Cohom 0 D) : ZMod (n : ℕ) :=
  localKummerTrace K n hn
    (cupTwoZero (G := GaloisGroup) (A := A) (B := D) (C := Mu) ev
      (discreteLinearDualIntEvaluation_continuous A Mu)
      (discreteLinearDualIntEvaluation_equivariant A Mu) x y)

end ClassFieldTheory.Brauer
