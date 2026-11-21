/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeStageModuleHom
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateDualExactness
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.MixedLocalProjectorReduction
public import Nyll.GaloisCohomology.GroupTheory.ModularProjectorHom

/-! # The actual degree-one Euler contribution at a coprime abelian stage -/

@[expose] public section

open CategoryTheory ContinuousCohomology LocalFieldTheory TopRep
open scoped IsMulCommutative Ring ValuativeRel MonoidAlgebra

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

private theorem exists_coprimeIntegralHomProjector {G : Type u} [CommGroup G] [Finite G]
    (p : ℕ) [Fact p.Prime] (V : ModuleCat.{u} ℤ[G]) [Finite V]
    (hV : ∀ x : V, p • x = 0) (hG : ¬ p ∣ Nat.card G) :
    ∃ (d : ℕ) (e : Matrix (Fin d) (Fin d) ((ZMod p)[G])) (he : IsIdempotentElem e),
      (∀ (W : ModuleCat.{u} ℤ[G]) [Finite W], (∀ x : W, p • x = 0) →
        Nat.card (V →ₗ[ℤ[G]] W) = MonoidAlgebra.primeProjectorCard (A := W) G e he Fact.out) := by
  let := MonoidAlgebra.modModule G p hV
  obtain ⟨d, e, he, hproj⟩ := MonoidAlgebra.exists_modularHomProjector G V hG
  refine ⟨d, e, he, fun W _ hW => ?_⟩
  let := MonoidAlgebra.modModule G p hW
  obtain ⟨eP⟩ := hproj W
  exact (Nat.card_congr ((MonoidAlgebra.modModuleHomEquiv G p hV hW).trans eP)).trans
    (MonoidAlgebra.primeProjectorCard_eq_modModule G e he Fact.out hW).symm

private theorem exists_coprimeIntegralHomProjectorLength {G : Type u} [CommGroup G] [Finite G]
    (p : ℕ) [Fact p.Prime] (V W M T Z : ModuleCat.{u} ℤ[G])
    [Finite V] [Finite W] [Finite M] [Finite T] [Finite Z]
    (hV : ∀ x : V, p • x = 0) (hW : ∀ x : W, p • x = 0) (hG : ¬ p ∣ Nat.card G)
    (c : ℕ) (hc : c = Nat.card (V →ₗ[ℤ[G]] W))
    (hlen : ∀ (d : ℕ) (e : Matrix (Fin d) (Fin d) ((ZMod p)[G])) (he : IsIdempotentElem e),
      MonoidAlgebra.primeProjectorLength G e he (Fact.out : p.Prime) W =
        MonoidAlgebra.primeProjectorLength G e he (Fact.out : p.Prime) M +
          MonoidAlgebra.primeProjectorLength G e he (Fact.out : p.Prime) T +
          MonoidAlgebra.primeProjectorLength G e he (Fact.out : p.Prime) Z) :
    ∃ (d : ℕ) (e : Matrix (Fin d) (Fin d) ((ZMod p)[G])) (he : IsIdempotentElem e),
      (∀ (Y : ModuleCat.{u} ℤ[G]) [Finite Y], (∀ y : Y, p • y = 0) →
        Nat.card (V →ₗ[ℤ[G]] Y) = MonoidAlgebra.primeProjectorCard (A := Y) G e he Fact.out) ∧
        (padicValNat p c : ℤ) = MonoidAlgebra.primeProjectorLength G e he (Fact.out : p.Prime) M +
          MonoidAlgebra.primeProjectorLength G e he (Fact.out : p.Prime) T +
          MonoidAlgebra.primeProjectorLength G e he (Fact.out : p.Prime) Z := by
  obtain ⟨d, e, he, hproj⟩ := exists_coprimeIntegralHomProjector p V hV hG
  exact ⟨d, e, he, hproj,
    (congrArg (fun k : ℕ => (padicValNat p k : ℤ)) (hc.trans (hproj W hW))).trans (hlen d e he)⟩

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [CharZero E]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    [IsIntegralClosure 𝒪[E] 𝒪[K] E] [Module.Finite 𝒪[K] 𝒪[E]]
    (p : ℕ) [Fact p.Prime]

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Q" => Gal(E/K)
local notation "F" => localGaloisGroupAlgebraFunctor K E
local notation "U" => ModuleCat.carrier (Functor.obj F (Rep.ofAlgebraAutOnUnits K E))
local notation "ML" => ModuleCat.carrier (Functor.obj F (normalBasisLatticeRep K E))
local notation "UL" => ModuleCat.carrier (Functor.obj F (localIntegerUnitRep K E))
local notation "VL" => ModuleCat.carrier (Functor.obj F (localValueRep K E))
local notation "Mu" => separableMuTopRep K p
local notation "n" => (Subtype.mk p (Nat.Prime.pos (Fact.out : p.Prime)) : ℕ+)
local notation "N[" X "]" => LinearMap.nsmulLinear (R := ℤ[Q]) p X
local notation "Qp[" X "]" => X ⧸ LinearMap.range (N[X])
local notation "Tp[" X "]" => LinearMap.ker (N[X])

attribute [local instance] coprimeStageSeparableClosureAlgebra

variable [IsMulCommutative Gal(E/K)]
    (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [Finite A] [DiscreteTopology A]
    (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ (h : ↥(stageOpenFixingSubgroup K E.toIntermediateField).toSubgroup) (a : A),
      A.ρ (h : Gal(SeparableClosure K/K)) a = a)
    (j : SeparableClosure K ≃ₐ[E] SeparableClosure E)

local notation "V" => ModuleCat.carrier (Functor.obj F (coprimeStageDualRep K E p ζ hζ A hfix))

include j

omit [IsIntegralClosure 𝒪[E] 𝒪[K] E] in
/-- The prime valuation of the actual first cohomology cardinal is the sum
of the three projected arithmetic contributions. The matrix projector
computes Hom out of the original Tate-dual module. -/
theorem exists_coprimeStageH1_projectorLength (hA : ∀ a : A, p • a = 0)
    (hdeg : ¬p ∣ Module.finrank K E) :
    let : Finite (Tp[UL]) := integerUnitPowerTorsion_finite K E p (Fact.out : p.Prime).ne_zero
    let : Finite (Qp[ML]) :=
      normalBasisLatticePowerQuotient_finite K E p (Fact.out : p.Prime).ne_zero
    let : Finite (Qp[VL]) := valueGroupPowerQuotient_finite K E p (Fact.out : p.Prime).pos
    ∃ (d : ℕ) (e : Matrix (Fin d) (Fin d) ((ZMod p)[Q])) (he : IsIdempotentElem e),
      (∀ (W : ModuleCat.{u} ℤ[Q]) [Finite W], (∀ x : W, p • x = 0) →
        Nat.card (V →ₗ[ℤ[Q]] W) = MonoidAlgebra.primeProjectorCard (A := W) Q e he
          (Fact.out : p.Prime)) ∧
        (padicValNat p (Nat.card (continuousCohomology 1 A)) : ℤ) =
          MonoidAlgebra.primeProjectorLength Q e he (Fact.out : p.Prime)
              (ModuleCat.of ℤ[Q] (Qp[ML])) +
            MonoidAlgebra.primeProjectorLength Q e he (Fact.out : p.Prime)
              (ModuleCat.of ℤ[Q] (Tp[UL])) +
            MonoidAlgebra.primeProjectorLength Q e he (Fact.out : p.Prime)
              (ModuleCat.of ℤ[Q] (Qp[VL])) := by
  intro hUL hML hVL
  let : Finite (Tp[UL]) := hUL
  let : Finite (Qp[ML]) := hML
  let : Finite (Qp[VL]) := hVL
  let hp : p.Prime := Fact.out
  let : Finite (Qp[U]) := fieldUnitPowerQuotient_finite K E p hp.pos
  let : Finite Mu := separableMuTopRep_finite K n (Nat.cast_ne_zero.mpr hp.ne_zero)
  let : Finite V := discreteLinearDual_finite A Mu
  have hV (l : V) : p • l = 0 := by
    let l' : discreteLinearDual A Mu := l
    exact separableMu_dual_nsmul_eq_zero K n A l'
  have hU (x : Qp[U]) : p • x = 0 := LinearMap.nsmul_powerQuotient_eq_zero p x
  have hQ : ¬p ∣ Nat.card Q := fun h => hdeg ((IsGalois.card_aut_eq_finrank K E) ▸ h)
  let eH := coprimeStageH1GroupAlgebraReductionHomEquiv K E p ζ hζ A hfix j
    (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hp.ne_zero) hA hdeg
  exact exists_coprimeIntegralHomProjectorLength p
    (ModuleCat.of ℤ[Q] V) (ModuleCat.of ℤ[Q] (Qp[U]))
    (ModuleCat.of ℤ[Q] (Qp[ML])) (ModuleCat.of ℤ[Q] (Tp[UL])) (ModuleCat.of ℤ[Q] (Qp[VL]))
    hV hU hQ (Nat.card (continuousCohomology 1 A)) (Nat.card_congr eH)
    (fun _ e he => localFieldUnits_primeProjectorLength K E p hp e he)

end ClassFieldTheory.Brauer
