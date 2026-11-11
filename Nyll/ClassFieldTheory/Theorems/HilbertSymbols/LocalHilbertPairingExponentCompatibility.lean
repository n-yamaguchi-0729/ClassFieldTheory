/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol

/-!
# Compatibility of Hilbert pairings at divisible exponents

Pairings constructed from the same arithmetic local Artin maps can be chosen
compatibly when `m ∣ n`. Their values are compared in `Kˣ`, since they belong
to different roots-of-unity subgroups. The public norm criterion places the
radical in the first argument. With that convention, the root-quotient
formula for arithmetic Artin has an inverse; the inverse occurs on both
sides of the exponent comparison and does not change the formula below.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u

/-- The named local Hilbert pairings from the specified Artin maps satisfy
exponent compatibility at the level of their actual values. -/
theorem localHilbertPairing_exponentCompatibility
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (m n : ℕ+) (hmK : ((m : ℕ) : K) ≠ 0)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmuM : (primitiveRoots (m : ℕ) K).Nonempty)
    (hmuN : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmn : (m : ℕ) ∣ (n : ℕ)) (a b : Kˣ) :
    (localHilbertPairing K m hmK hmuM
      (powerClass K m a) (powerClass K m b)).1 =
      (localHilbertPairing K n hnK hmuN
        (powerClass K n a) (powerClass K n b)).1 ^
          ((n : ℕ) / (m : ℕ)) := by
  rw [localHilbertPairing_powerClass, localHilbertPairing_powerClass]
  change (LocalClassFieldTheory.Kummer.localHilbertSymbol K m hmK hmuM a b).1 =
    (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmuN a b).1 ^
      ((n : ℕ) / (m : ℕ))
  exact LocalClassFieldTheory.Kummer.localHilbertSymbol_exponentCompatibility
    K m n hmK hnK hmuM hmuN hmn a b

/-- For `m ∣ n`, the named local Hilbert pairings at exponents `m` and `n`
satisfy `(a,b)ₘ = (a,b)ₙ ^ (n/m)` in the base-field unit group. Neither
pairing is asserted to be determined by the algebraic laws alone. -/
theorem exists_compatibleLocalHilbertPairings_of_dvd
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (m n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmuN : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmn : (m : ℕ) ∣ (n : ℕ)) :
    ∃ Bm : HilbertPairing K m,
      HilbertPairing.IsLocalHilbertPairing Bm ∧
      ∃ Bn : HilbertPairing K n,
        HilbertPairing.IsLocalHilbertPairing Bn ∧
        ∀ a b : Kˣ,
          (Bm (powerClass K m a) (powerClass K m b)).1 =
            (Bn (powerClass K n a) (powerClass K n b)).1 ^
              ((n : ℕ) / (m : ℕ)) := by
  obtain ⟨q, hq⟩ := hmn
  have hmK : ((m : ℕ) : K) ≠ 0 := by
    intro hz
    apply hnK
    rw [hq, Nat.cast_mul, hz, zero_mul]
  have hmuM : (primitiveRoots (m : ℕ) K).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmuN
    refine ⟨ζ ^ q, (mem_primitiveRoots m.pos).2 ?_⟩
    exact IsPrimitiveRoot.pow n.pos ((mem_primitiveRoots n.pos).1 hζ)
      (by rw [mul_comm]; exact hq)
  refine ⟨localHilbertPairing K m hmK hmuM,
    localHilbertPairing_isLocalHilbertPairing K m hmK hmuM,
    localHilbertPairing K n hnK hmuN,
    localHilbertPairing_isLocalHilbertPairing K n hnK hmuN, ?_⟩
  exact localHilbertPairing_exponentCompatibility K m n hmK hnK hmuM hmuN ⟨q, hq⟩

end ClassFieldTheory
