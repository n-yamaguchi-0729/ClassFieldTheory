/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePrimeDescent
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateTrivialEndpoints

/-! # Perfectness of the actual local Tate pairing -/

@[expose] public section

open scoped ValuativeRel
open ClassFieldTower.Cohomology LocalFieldTheory

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

local notation "G" => Gal(SeparableClosure K/K)

/-- All three canonical adjoints for the trivial prime line are bijective
over a local field containing a primitive root of the given order. -/
theorem localTatePairingAdjoints_bijective_trivialPrime (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    let A := trivialIntegralZModPLifted p G
    let : DiscreteTopology A := localTateTrivialCoefficient_discrete K p
    Function.Bijective (localTatePairingZeroAdjoint K ⟨p, hp.pos⟩ A hpK) ∧
      Function.Bijective (localTatePairingOneAdjoint K ⟨p, hp.pos⟩ A hpK) ∧
      Function.Bijective (localTatePairingTwoAdjoint K ⟨p, hp.pos⟩ A hpK) := by
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨localTatePairingZeroAdjoint_bijective_trivialPrime K p hpK,
    localTatePairingOneAdjoint_bijective_trivialPrime K p hpK,
    localTatePairingTwoAdjoint_bijective_trivialPrime K p hpK hζ⟩

/-- The local Tate pairing on finite discrete coefficients annihilated by
an étale exponent is perfect in complementary degrees zero, one and two. -/
theorem localTatePairingAdjoints_bijective (n : ℕ+) (A : TopRep.{u} ℤ G)
    [Finite A] [DiscreteTopology A] (hn : ((n : ℕ) : K) ≠ 0)
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (hAn : ∀ a : A, (n : ℕ) • a = 0) :
    Function.Bijective (localTatePairingZeroAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingOneAdjoint K n A hn) ∧
      Function.Bijective (localTatePairingTwoAdjoint K n A hn) := by
  apply localTatePairingAdjoints_bijective_of_trivialPrimeLine K n A hn ?_ hA hAn
  intro F _ _ _ _ p hp hpF ζ hζ
  exact localTatePairingAdjoints_bijective_trivialPrime F p hp.out hpF hζ

end ClassFieldTheory.Brauer
