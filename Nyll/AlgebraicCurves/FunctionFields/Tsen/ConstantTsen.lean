/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantSeparatingParameter
import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveIffTranscendentalFiniteDimensional
import Nyll.AlgebraicCurves.FunctionFields.Tsen.NormSurjectiveOfTsen
import Nyll.AlgebraicCurves.FunctionFields.Tsen.GaloisH2OfTsen

/-!
# Tsen for the actual algebraic extension of constants

Transport a separating parameter from the original field using the actual
generation by constants. Algebraicity of the extended constants preserves
transcendence, giving the input to norm surjectivity and actual unit H² vanishing.
-/

noncomputable section

namespace AlgebraicCurve

variable {k Ω K F : Type} [Field k] [PerfectField k] [Field Ω] [Field K] [Field F]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Algebra k K] [IsCurveOver k K] [Algebra.EssFiniteType k K]
    [Algebra Ω F] [Algebra K F] [Algebra k F]
    [IsScalarTower k Ω F] [IsScalarTower k K F]

include k

/-- The actual algebraic constant base change has a separating transcendental parameter. -/
theorem exists_separatingParameter_constantBaseChange
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap K F)) = ⊤) :
    ∃ t : F, Transcendental Ω t ∧
      FiniteDimensional (IntermediateField.adjoin Ω ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin Ω ({t} : Set F)) F := by
  obtain ⟨t, ht, hfin, hsep⟩ :=
    (isCurveOver_iff_exists_transcendental_finiteDimensional (K := k) (F := K)).mp
      (inferInstance : IsCurveOver k K)
  have htF : Transcendental k (algebraMap K F t) :=
    (transcendental_algebraMap_iff (algebraMap K F).injective).mpr ht
  obtain ⟨hfinF, hsepF⟩ := finite_separable_adjoin_constantBaseChange
    (K := k) (F := K) (K' := Ω) (F' := F) t hgen
  exact ⟨algebraMap K F t, htF.extendScalars Ω, hfinF, hsepF⟩

/-- The curve API is supplied by the actual original-field and constant-field embeddings. -/
theorem isCurveOver_constantBaseChange
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap K F)) = ⊤) :
    IsCurveOver Ω F := by
  obtain ⟨t, ht, hfin, hsep⟩ := exists_separatingParameter_constantBaseChange (k := k) hgen
  exact isCurveOver_of_transcendental ht hfin hsep

variable [IsAlgClosed Ω]

/-- Every finite extension of the actual geometric constant field has surjective field norm. -/
theorem norm_surjective_constantBaseChange
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap K F)) = ⊤)
    (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] :
    Function.Surjective (Algebra.norm F : L →* F) := by
  obtain ⟨t, ht, hfin, hsep⟩ := exists_separatingParameter_constantBaseChange (k := k) hgen
  exact norm_surjective_of_transcendental_of_finiteDimensional Ω t ht hfin hsep L

/-- Actual finite Galois unit H² vanishes after the proved geometric constant base change. -/
theorem galoisUnitsH2_eq_zero_constantBaseChange
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap K F)) = ⊤)
    (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) : c = 0 := by
  obtain ⟨t, ht, hfin, -⟩ := exists_separatingParameter_constantBaseChange (k := k) hgen
  exact galoisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional Ω t ht hfin L c

end AlgebraicCurve
