/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimePowerClasses
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.MixedPrimePowerClasses
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
public import Nyll.GaloisCohomology.GroupTheory.PrimeProjectorReduction
public import Mathlib.RepresentationTheory.Rep.Iso

/-! # Projected power classes of mixed-characteristic local units -/

@[expose] public section

open CategoryTheory LocalFieldTheory LocalClassFieldTheory CyclicCohomology
open scoped IsMulCommutative MonoidAlgebra Ring ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u v

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

local notation "G" => Gal(L/K)
local notation "M" => chosenNormalBasisIntegerLattice K L

/-- The actual restricted Galois action on the chosen normal-basis lattice. -/
def normalBasisLatticeRep : Rep.{u} ℤ G :=
  Rep.of {
    toFun := fun σ =>
      ((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ).restrictScalars ℤ).toLinearMap
    map_one' := LinearMap.ext fun _ => Subtype.ext rfl
    map_mul' := fun _ _ => LinearMap.ext fun _ => Subtype.ext rfl }

/-- The group-algebra module functor on the original local Galois group. -/
abbrev localGaloisGroupAlgebraFunctor : Rep.{u} ℤ G ⥤ ModuleCat.{u} ℤ[G] :=
  Rep.toModuleMonoidAlgebra

local notation "F" => localGaloisGroupAlgebraFunctor K L
local notation "ML" => ModuleCat.carrier (Functor.obj F (normalBasisLatticeRep K L))
local notation "UL" => ModuleCat.carrier (Functor.obj F (localIntegerUnitRep K L))
local notation "FL" => ModuleCat.carrier (Functor.obj F (Rep.ofAlgebraAutOnUnits K L))
local notation "VL" => ModuleCat.carrier (Functor.obj F (localValueRep K L))
local notation "N[" n "," X "]" => (n • (LinearMap.id : X →ₗ[ℤ[G]] X))
local notation "Q[" n "," X "]" => X ⧸ LinearMap.range (N[n,X])
local notation "T[" n "," X "]" => LinearMap.ker (N[n,X])

omit [CharZero K] in
/-- The actual finite-index normal-basis inclusion is a map over the integral
group algebra, with the original action on the integer units. -/
theorem exists_normalBasisLatticeGroupAlgebraMap :
    ∃ f : ML →ₗ[ℤ[G]] UL, Function.Injective f ∧ Finite (UL ⧸ LinearMap.range f) := by
  obtain ⟨f, hf, hQ, hgal⟩ := exists_normalBasisLattice_integerUnits_finite_quotient K L
  let j : normalBasisLatticeRep K L ⟶ localIntegerUnitRep K L :=
    Rep.ofHom (f.intertwiningMap_of_isIntertwiningMap
      (normalBasisLatticeRep K L).ρ (localIntegerUnitRep K L).ρ (fun σ x =>
        congrArg Additive.ofMul (hgal σ x)))
  exact ⟨((F).map j).hom, hf, hQ⟩

private theorem finite_baseIntegerRingPowerQuotient (n : ℕ) (hn : n ≠ 0) :
    Finite (𝒪[K] ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ) n 𝒪[K])) := by
  let A := (LinearMap.range (LinearMap.nsmulLinear (R := ℤ) n 𝒪[K])).toAddSubgroup
  have hK : IsOpen (𝒪[K] : Set K) := (ValuativeRel.valuation K).isOpen_integer
  have hcast : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hA : (A : Set 𝒪[K]) = (Subtype.val : 𝒪[K] → K) ⁻¹'
      ((fun y : K => (n : K) * y) '' (𝒪[K] : Set K)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, (nsmul_eq_mul n (y : K)).symm⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext ((nsmul_eq_mul n y).trans hxy)⟩
  have hOpen : IsOpen (A : Set 𝒪[K]) := by
    rw [hA]
    exact ((isOpenMap_smul₀ hcast) _ hK).preimage continuous_subtype_val
  exact AddSubgroup.quotient_finite_of_isOpen A hOpen

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]] in
theorem normalBasisLatticePowerQuotient_finite (n : ℕ) (hn : n ≠ 0) : Finite (Q[n,ML]) := by
  let : Finite (𝒪[K] ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ) n 𝒪[K])) :=
    finite_baseIntegerRingPowerQuotient K n hn
  exact Finite.of_equiv _ (normalBasisPowerCoordinates K L n).toEquiv.symm

omit [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]] in
theorem fieldUnitPowerQuotient_finite (n : ℕ) (hn : 0 < n) : Finite (Q[n,FL]) := by
  let A := Multiplicative (Additive Lˣ)
  let : Finite (A ⧸ (powMonoidHom n : A →* A).range) :=
    finite_nthPowerQuotient_of_natCast_ne_zero L n (Nat.cast_ne_zero.mpr hn.ne')
  exact Finite.of_equiv _ (multiplicativeNthPowerQuotientEquivAdditive (Additive Lˣ) n)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  [Module.Finite 𝒪[K] 𝒪[L]] in
theorem integerUnitPowerQuotient_finite (n : ℕ) (hn : 0 < n) : Finite (Q[n,UL]) := by
  let : Finite (Rep.powerReduction (Rep.ofAlgebraAutOnUnits K L) n) :=
    fieldUnitPowerQuotient_finite K L n hn
  exact Finite.of_injective (localIntegerUnitPowerClassInclusion K L n)
    (localPowerClassValuation_exact K L n hn).1

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  [Module.Finite 𝒪[K] 𝒪[L]] in
theorem valueGroupPowerQuotient_finite (n : ℕ) (hn : 0 < n) : Finite (Q[n,VL]) := by
  let : Finite (Rep.powerReduction (Rep.ofAlgebraAutOnUnits K L) n) :=
    fieldUnitPowerQuotient_finite K L n hn
  exact Finite.of_surjective (localPowerClassValuation K L n)
    (localPowerClassValuation_exact K L n hn).2.2

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
  [Module.Finite 𝒪[K] 𝒪[L]] in
theorem integerUnitPowerTorsion_finite (n : ℕ) (hn : n ≠ 0) : Finite (T[n,UL]) := by
  let : NeZero n := ⟨hn⟩
  let f : T[n,UL] → rootsOfUnity n 𝒪[L] := fun x => ⟨x.val.toMul, by
    let a : Additive 𝒪[L]ˣ := x.val
    have hx : n • a = 0 := x.property
    exact (mem_rootsOfUnity _ _).mpr
      (congrArg (Additive.toMul : Additive 𝒪[L]ˣ → 𝒪[L]ˣ) hx)⟩
  exact Finite.of_injective f (fun _ _ h => Subtype.ext
    (Additive.toMul.injective (congrArg Subtype.val h)))

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]] in
private theorem normalBasisLattice_nsmul_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (N[n,ML]) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun x : ML => ((show M from x) : L)) hab
  change n • ((show M from a) : L) = n • ((show M from b) : L) at h
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn) h

/-- For mixed-characteristic integer units, the actual projected prime
power classes equal the normal-basis reduction plus the roots-of-unity kernel. -/
theorem localIntegerUnits_primeProjectorLength (p : ℕ) (hp : p.Prime) [IsMulCommutative G]
    {J : Type v} [Fintype J] [DecidableEq J]
    (e : Matrix J J ((ZMod p)[G])) (he : IsIdempotentElem e) :
    letI : Finite (T[p,UL]) := integerUnitPowerTorsion_finite K L p hp.ne_zero
    letI : Finite (Q[p,UL]) := integerUnitPowerQuotient_finite K L p hp.pos
    letI : Finite (Q[p,ML]) := normalBasisLatticePowerQuotient_finite K L p hp.ne_zero
    MonoidAlgebra.primeProjectorLength G e he hp (ModuleCat.of ℤ[G] (Q[p,UL])) =
      MonoidAlgebra.primeProjectorLength G e he hp (ModuleCat.of ℤ[G] (Q[p,ML])) +
        MonoidAlgebra.primeProjectorLength G e he hp (ModuleCat.of ℤ[G] (T[p,UL])) := by
  let : Finite (T[p,UL]) := integerUnitPowerTorsion_finite K L p hp.ne_zero
  let : Finite (Q[p,UL]) := integerUnitPowerQuotient_finite K L p hp.pos
  let : Finite (Q[p,ML]) := normalBasisLatticePowerQuotient_finite K L p hp.ne_zero
  obtain ⟨f, hf, hF⟩ := exists_normalBasisLatticeGroupAlgebraMap K L
  let D := LinearMap.range f
  let : Finite (UL ⧸ D) := hF
  exact MonoidAlgebra.primeProjectorLength_powerReduction_of_finite_quotient G e he hp
    f D.mkQ hf D.mkQ_surjective (LinearMap.exact_map_mkQ_range f)
    (normalBasisLattice_nsmul_injective K L p hp.ne_zero)

/-- The field power classes have the projected weight of the normal-basis
reduction, the original torsion units, and the trivial valuation reduction. -/
theorem localFieldUnits_primeProjectorLength (p : ℕ) (hp : p.Prime) [IsMulCommutative G]
    {J : Type v} [Fintype J] [DecidableEq J]
    (e : Matrix J J ((ZMod p)[G])) (he : IsIdempotentElem e) :
    letI : Finite (T[p,UL]) := integerUnitPowerTorsion_finite K L p hp.ne_zero
    letI : Finite (Q[p,FL]) := fieldUnitPowerQuotient_finite K L p hp.pos
    letI : Finite (Q[p,ML]) := normalBasisLatticePowerQuotient_finite K L p hp.ne_zero
    letI : Finite (Q[p,VL]) := valueGroupPowerQuotient_finite K L p hp.pos
    MonoidAlgebra.primeProjectorLength G e he hp (ModuleCat.of ℤ[G] (Q[p,FL])) =
      MonoidAlgebra.primeProjectorLength G e he hp (ModuleCat.of ℤ[G] (Q[p,ML])) +
        MonoidAlgebra.primeProjectorLength G e he hp (ModuleCat.of ℤ[G] (T[p,UL])) +
          MonoidAlgebra.primeProjectorLength G e he hp (ModuleCat.of ℤ[G] (Q[p,VL])) := by
  let : Finite (T[p,UL]) := integerUnitPowerTorsion_finite K L p hp.ne_zero
  let : Finite (Q[p,FL]) := fieldUnitPowerQuotient_finite K L p hp.pos
  let : Finite (Q[p,ML]) := normalBasisLatticePowerQuotient_finite K L p hp.ne_zero
  let : Finite (Q[p,VL]) := valueGroupPowerQuotient_finite K L p hp.pos
  let : Finite (Q[p,UL]) := integerUnitPowerQuotient_finite K L p hp.pos
  let f := ((F).map (localIntegerUnitInclusion K L)).hom
  let g := ((F).map (localUnitValuation K L)).hom
  obtain ⟨hf, hex, hg⟩ := localUnitValuation_exact K L
  have hZ : Function.Injective (N[p,VL]) := localValue_nsmul_injective K L p hp.pos
  have hPower := MonoidAlgebra.primeProjectorLength_add_of_exact G e he hp
    (ModuleCat.of ℤ[G] (Q[p,UL])) (ModuleCat.of ℤ[G] (Q[p,FL])) (ModuleCat.of ℤ[G] (Q[p,VL]))
    (LinearMap.powerReductionMap p f) (LinearMap.powerReductionMap p g)
    (LinearMap.powerReductionMap_injective_of_quotient p f g hf hg hex hZ)
    (LinearMap.powerReductionMap_surjective p g hg)
    (LinearMap.powerReduction_exact p f g hg hex)
  rw [hPower, localIntegerUnits_primeProjectorLength K L p hp e he]

end ClassFieldTheory.Brauer
