/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeStageModuleHom
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.MixedLocalProjectorReduction
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Algebra.Module.ZMod

/-! # The regular normal-basis term in the coprime Euler calculation -/

@[expose] public section

open CategoryTheory LocalClassFieldTheory LocalFieldTheory
open scoped Ring MonoidAlgebra ValuativeRel

noncomputable section

namespace Rep

universe u

variable {G : Type u} [Group G] (A : Rep.{u} ℤ G) (n : ℕ)

local notation "F" => Rep.toModuleMonoidAlgebra (k := ℤ) (G := G)
local notation "S" => LinearMap.range (LinearMap.nsmulLinear (R := ℤ) n A)
local notation "Aq" => Rep.powerReduction A n
local notation "LA" => ModuleCat.carrier (Functor.obj F A)
local notation "LQ" => ModuleCat.carrier (Functor.obj F Aq)

/-- Forgetting the representation to a group-algebra module preserves the
quotient by integral powers, including the original module structure. -/
def powerReductionModuleEquiv :
    (LA ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ[G]) n LA)) ≃ₗ[ℤ[G]] LQ := by
  let projection : A ⟶ Aq := by
    let : Module ℤ A := A.hV2
    let : Module ℤ (A ⧸ S) := (Aq).hV2
    let q : A →ₗ[ℤ] (A ⧸ S) := (S).mkQ
    exact Rep.ofHom (q.intertwiningMap_of_isIntertwiningMap A.ρ (Aq).ρ (fun g a =>
      (LinearMap.powerReductionMap_mkQ n (A.ρ g) a).symm))
  let q : LA →ₗ[ℤ[G]] LQ := ((F).map projection).hom
  have hq : Function.Surjective q := by
    intro x
    let x' : A ⧸ S := x
    obtain ⟨y, hy⟩ := (S).mkQ_surjective x'
    exact ⟨y, hy⟩
  have hker : LinearMap.range (LinearMap.nsmulLinear (R := ℤ[G]) n LA) =
      LinearMap.ker q := by
    ext x
    let x' : A := x
    change (∃ y : A, n • y = x') ↔ (S).mkQ x' = 0
    exact (Submodule.Quotient.mk_eq_zero S).symm
  exact (Submodule.quotEquivOfEq _ _ hker).trans (q.quotKerEquivOfSurjective hq)

end Rep

namespace ClassFieldTheory.Brauer

universe u

private theorem card_zmodHom_of_targetCard (p : ℕ) [Fact p.Prime] (A X : Type u)
    [AddCommGroup A] [Module (ZMod p) A] [Finite A]
    [AddCommGroup X] [Module (ZMod p) X] [Finite X]
    (h : ℕ) (hX : Nat.card X = p ^ h) :
    Nat.card (A →ₗ[ZMod p] X) = Nat.card A ^ h := by
  have hdim : Module.finrank (ZMod p) X = h := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ Module.finrank (ZMod p) X =
          Nat.card (ZMod p) ^ Module.finrank (ZMod p) X := by rw [Nat.card_zmod]
      _ = Nat.card X := (Module.natCard_eq_pow_finrank (K := ZMod p) (V := X)).symm
      _ = p ^ h := hX
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := A →ₗ[ZMod p] X),
    Module.finrank_linearMap (ZMod p) (ZMod p) A X, hdim,
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := A), pow_mul]

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K]

local notation "Γfinite" => Gal(L/K)
local notation "X[" n "]" =>
  𝒪[K] ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ) n 𝒪[K])
local notation "M" => normalBasisLatticeRep K L

/-- An equivariant map into the regular normal-basis quotient is determined
by its identity coordinate. The other coordinates are obtained by the
inverse Galois action on the input. -/
def normalBasisPowerReductionHomEquiv (n : ℕ) (A : Rep.{u} ℤ Γfinite) :
    (A ⟶ Rep.powerReduction M n) ≃ (A →ₗ[ℤ] X[n]) := by
  let N := Rep.powerReduction M n
  let e : N ≃ₗ[ℤ] (Γfinite → X[n]) := normalBasisPowerCoordinates K L n
  have he (g h : Γfinite) (y : N) : e (N.ρ g y) h = e y (g⁻¹ * h) :=
    normalBasisPowerCoordinates_galois K L n g h y
  let eval : N →ₗ[ℤ] X[n] := (LinearMap.proj 1).comp e.toLinearMap
  let lift (ℓ : A →ₗ[ℤ] X[n]) : A →ₗ[ℤ] N :=
    e.symm.toLinearMap.comp (LinearMap.pi fun h => ℓ.comp (A.ρ h⁻¹))
  have hlift (ℓ : A →ₗ[ℤ] X[n]) (x : A) (h : Γfinite) :
      e (lift ℓ x) h = ℓ (A.ρ h⁻¹ x) :=
    congrFun (e.apply_symm_apply (fun g => ℓ (A.ρ g⁻¹ x))) h
  refine
    { toFun := fun φ => eval.comp φ.hom.toLinearMap
      invFun := fun ℓ => Rep.ofHom ((lift ℓ).intertwiningMap_of_isIntertwiningMap A.ρ N.ρ ?_)
      left_inv := ?_
      right_inv := ?_ }
  · intro g x
    apply e.injective
    funext h
    rw [hlift, he, hlift, mul_inv_rev, inv_inv, map_mul]
    rfl
  · intro φ
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply e.injective
    funext h
    change e (lift (eval.comp φ.hom.toLinearMap) x) h = e (φ.hom x) h
    rw [hlift, LinearMap.comp_apply]
    have hφ := Representation.IntertwiningMap.isIntertwining A.ρ N.ρ φ.hom h⁻¹ x
    change e (φ.hom (A.ρ h⁻¹ x)) 1 = e (φ.hom x) h
    rw [hφ, he, inv_inv, mul_one]
  · intro ℓ
    apply LinearMap.ext
    intro x
    change e (lift ℓ x) 1 = ℓ x
    rw [hlift, inv_one, map_one, one_apply_eq_self]

open LocalFieldTheory.DiscreteValuationField

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

local notation "F" => localGaloisGroupAlgebraFunctor K L
local notation "ML" => ModuleCat.carrier (Functor.obj F M)
local notation "L[" n "]" =>
  ML ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ[Γfinite]) n ML)
local notation "LRep[" A "]" => ModuleCat.carrier (Functor.obj F A)

/-- The actual regular contribution has one copy of the finite coefficient
module for each residue-prime exponent in the local order norm. -/
theorem card_normalBasisPowerHom (p : ℕ) [Fact p.Prime]
    (A : Rep.{u} ℤ Γfinite) [Finite A] (hA : ∀ a : A, p • a = 0) :
    let v := localIntegerValuation K
    let P := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
    Nat.card (LRep[A] →ₗ[ℤ[Γfinite]] L[p]) =
      Nat.card A ^ (Module.finrank ℚ_[P.residueCharacteristic] K *
        padicValNat P.residueCharacteristic p) := by
  let v := localIntegerValuation K
  let P := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  let q := P.residueCharacteristic
  let d := Module.finrank ℚ_[q] K
  let h := d * padicValNat q p
  let : Fact q.Prime := ⟨P.residueCharacteristic_prime⟩
  let hp : p.Prime := Fact.out
  let e := Rep.powerReductionModuleEquiv M p
  let e₀ : (LRep[A] →ₗ[ℤ[Γfinite]] L[p]) ≃
      (LRep[A] →ₗ[ℤ[Γfinite]] LRep[Rep.powerReduction M p]) :=
    { toFun := fun f => e.toLinearMap.comp f
      invFun := fun f => e.symm.toLinearMap.comp f
      left_inv := fun f => LinearMap.ext fun x => e.symm_apply_apply (f x)
      right_inv := fun f => LinearMap.ext fun x => e.apply_symm_apply (f x) }
  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℤ) (G := Γfinite)
  let e₁ := ModuleCat.homEquiv.symm.trans (E.fullyFaithfulFunctor.homEquiv (X := A)
    (Y := Rep.powerReduction M p)).symm
  let e₂ := normalBasisPowerReductionHomEquiv K L p A
  let : Module (ZMod p) A := AddCommGroup.zmodModule hA
  let : Module (ZMod p) (X[p]) := AddCommGroup.zmodModule (LinearMap.nsmul_powerQuotient_eq_zero p)
  let e₃ : (A →ₗ[ℤ] X[p]) ≃ (A →ₗ[ZMod p] X[p]) :=
    { toFun := fun f => f.toAddMonoidHom.toZModLinearMap p
      invFun := fun f =>
        let t : A →+ X[p] := f.toAddMonoidHom
        { toFun := t
          map_add' := t.map_add
          map_smul' := fun z x =>
            (congrArg t (int_smul_eq_zsmul A.hV2 z x)).trans
              ((map_zsmul t z x).trans (int_smul_eq_zsmul (inferInstance : Module ℤ (X[p])) z
                (t x)).symm) }
      left_inv := fun _ => LinearMap.ext fun _ => rfl
      right_inv := fun _ => LinearMap.ext fun _ => rfl }
  have hX : Nat.card (X[p]) = p ^ h := by
    rw [card_baseIntegerRingPowerQuotient K p hp.ne_zero]
    change (q ^ padicValNat q p) ^ d = p ^ (d * padicValNat q p)
    rw [Nat.padicValNat_def]
    by_cases hpq : q = p
    · have hpp : multiplicity p p = 1 := Nat.Prime.multiplicity_self
      simp only [hpq, hpp, pow_one, mul_one]
    · have hqp : multiplicity q p = 0 := multiplicity_primes hpq
      simp only [hqp, pow_zero, one_pow, mul_zero]
  let : Finite (X[p]) :=
    Nat.finite_of_card_ne_zero (fun hz => pow_ne_zero h hp.ne_zero (hX.symm.trans hz))
  change Nat.card (LRep[A] →ₗ[ℤ[Γfinite]] L[p]) = Nat.card A ^ h
  exact (Nat.card_congr (((e₀.trans e₁).trans e₂).trans e₃)).trans
    (card_zmodHom_of_targetCard p A (X[p]) h hX)

end ClassFieldTheory.Brauer
