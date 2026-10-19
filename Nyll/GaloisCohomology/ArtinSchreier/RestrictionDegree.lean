/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.RestrictionKernelCharacterEquiv
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Galois.Abelian

/-!
# Degree bounds from actual split Artin–Schreier classes

The established root-character equivalence sends split parameter classes
injectively to prime cyclic characters. In an elementary abelian extension,
finite-dimensional linear duality counts those characters by the actual
extension degree.
-/

noncomputable section
namespace ArtinSchreierTheory

private theorem card_primeCharacters
    (p : ℕ) [Fact p.Prime] (G : Type*) [CommGroup G] [Finite G]
    (hp : ∀ g : G, g ^ p = 1) :
    Nat.card (G →* Multiplicative (ZMod p)) = Nat.card G := by
  let zmodStructure : Module (ZMod p) (Additive G) :=
    AddCommGroup.zmodModule (fun x => hp x.toMul)
  have hfinite : Module.Finite (ZMod p) (Additive G) := Module.Finite.of_finite
  calc
    Nat.card (G →* Multiplicative (ZMod p)) =
        Nat.card (Additive G →+ ZMod p) := Nat.card_congr MonoidHom.toAdditiveLeft
    _ = Nat.card (Module.Dual (ZMod p) (Additive G)) :=
      Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv p).toEquiv
    _ = Nat.card (Additive G) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Subspace.dual_finrank_eq,
        ← Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G)]
    _ = Nat.card G := Nat.card_congr Additive.toMul

open scoped IsMulCommutative in
/-- A finite elementary abelian extension splits at most its degree many
Artin–Schreier parameter classes. -/
theorem card_classMap_kernel_le_finrank
    (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L]
    [CharP K p] [CharP L p] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (hexp : ∀ σ : Gal(L/K), σ ^ p = 1) :
    Nat.card (classMap p (algebraMap K L)).ker ≤ Module.finrank K L := by
  have hfinite : Finite (classMap p (algebraMap K L)).ker := finite_classMap_kernel p
  have hchars : Finite (Gal(L/K) →* Multiplicative (ZMod p)) :=
    Finite.of_injective (fun χ : Gal(L/K) →* Multiplicative (ZMod p) =>
      (χ : Gal(L/K) → Multiplicative (ZMod p))) DFunLike.coe_injective
  let e := restrictionKernelEquivCharacters p (K := K) (L := L)
  have hbound : Nat.card (Multiplicative (classMap p (algebraMap K L)).ker) ≤
      Nat.card (Gal(L/K) →* Multiplicative (ZMod p)) :=
    Nat.card_le_card_of_injective
      (fun x => (e x).toMonoidHom)
      (ContinuousMonoidHom.toMonoidHom_injective.comp e.injective)
  rw [card_primeCharacters p Gal(L/K) hexp, IsGalois.card_aut_eq_finrank K L] at hbound
  exact hbound

end ArtinSchreierTheory
