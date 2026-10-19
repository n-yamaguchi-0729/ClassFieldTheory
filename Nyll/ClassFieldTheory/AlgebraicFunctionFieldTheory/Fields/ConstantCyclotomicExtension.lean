/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGalois

/-!
# Supplying Kummer roots of unity by an actual constant extension

A root of unity of order prime to the characteristic is algebraic over the
finite constant field. Adjoining it there gives a finite constant field inside
the original separably closed ambient field. Its actual compositum with the
function field therefore contains the same primitive root. The extension is
formed by the existing finite Galois constant-stage construction.
-/

noncomputable section

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω]

/-- Every order prime to the characteristic acquires a primitive root in an
actual finite constant extension of the original field. -/
theorem exists_constantStage_primitiveRoot (n : ℕ) [NeZero (n : k)] :
    ∃ C : FiniteGaloisIntermediateField k Ω,
      (primitiveRoots n (constantExtensionStage (K := K) C.toIntermediateField)).Nonempty := by
  have hn : NeZero n := NeZero.of_neZero_natCast k
  have hnΩ : NeZero (n : Ω) := by
    simpa only [map_natCast] using
      (inferInstance : NeZero (n : k)).of_injective (algebraMap k Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hζintegral : IsIntegral k ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hn.out) (by
    rw [hζ.pow_eq_one]
    exact isIntegral_one)
  let C : IntermediateField k Ω := IntermediateField.adjoin k {ζ}
  have hCdim : FiniteDimensional k C := IntermediateField.adjoin.finiteDimensional hζintegral
  have hCfinite : Finite C := Module.finite_of_finite k
  let Cg : FiniteGaloisIntermediateField k Ω := { toIntermediateField := C }
  let ζC : C := ⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩
  have hζC : IsPrimitiveRoot ζC n :=
    IsPrimitiveRoot.of_map_of_injective (f := C.val) hζ C.val.injective
  let iC : C →ₐ[k] constantExtensionStage (K := K) C := constantEmbedding (K := K) C
  refine ⟨Cg, iC ζC, (mem_primitiveRoots (Nat.pos_of_ne_zero hn.out)).mpr ?_⟩
  exact hζC.map_of_injective iC.injective

end FunctionField
