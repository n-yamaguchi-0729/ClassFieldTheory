/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantSeparatingParameter
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveIffTranscendentalFiniteDimensional
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.NormSurjectiveOfTsen
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.GaloisH2OfTsen
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.EtaleCohomologyOfTsen

/-!
# Tsen for the actual algebraic extension of constants

Transport a separating parameter from the original field using the actual
generation by constants. Algebraicity of the extended constants preserves
transcendence, giving the input to norm surjectivity and actual unit H² vanishing.
-/

@[expose] public section

universe u v w x y

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicCurve

section Algebraic

variable {k : Type u} {Ω : Type v} {K : Type w} {F : Type x}
    [Field k] [PerfectField k] [Field Ω] [Field K] [Field F]
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
    (L : Type y) [Field L] [Algebra F L] [FiniteDimensional F L] :
    Function.Surjective (Algebra.norm F : L →* F) := by
  obtain ⟨t, ht, hfin, hsep⟩ := exists_separatingParameter_constantBaseChange (k := k) hgen
  exact norm_surjective_of_transcendental_of_finiteDimensional Ω t ht hfin hsep L

end Algebraic

section NativeCohomology

variable {k Ω K F : Type} [Field k] [PerfectField k] [Field Ω] [Field K] [Field F]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Algebra k K] [IsCurveOver k K] [Algebra.EssFiniteType k K]
    [Algebra Ω F] [Algebra K F] [Algebra k F]
    [IsScalarTower k Ω F] [IsScalarTower k K F]

include k

variable [IsAlgClosed Ω]

/-- Actual finite Galois unit H² vanishes after the proved geometric constant base change. -/
theorem galoisUnitsH2_eq_zero_constantBaseChange
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap K F)) = ⊤)
    (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) : c = 0 := by
  obtain ⟨t, ht, hfin, -⟩ := exists_separatingParameter_constantBaseChange (k := k) hgen
  exact galoisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional Ω t ht hfin L c

end NativeCohomology

section EtaleCohomology

variable {k : Type u} {Ω : Type v} {K : Type w} {F : Type v}
    [Field k] [PerfectField k] [Field Ω] [Field K] [Field F]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Algebra k K] [IsCurveOver k K] [Algebra.EssFiniteType k K]
    [Algebra Ω F] [Algebra K F] [Algebra k F]
    [IsScalarTower k Ω F] [IsScalarTower k K F] [IsAlgClosed Ω]

include k

/-- Bounded-torsion étale cohomology of the actual geometric function field
vanishes above degree one. The parameter is obtained from the original curve
and the actual generation by algebraic constants. -/
theorem fieldEtale_cohomology_eq_zero_constantBaseChange
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap K F)) = ⊤)
    (S : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{v})
    (m : ℤ) (hm0 : m ≠ 0) (hm : m • 𝟙 S = 0)
    (n : ℕ) (v : Sheaf.H.{v} S (n + 2)) : v = 0 := by
  obtain ⟨t, ht, hfin, -⟩ := exists_separatingParameter_constantBaseChange (k := k) hgen
  exact fieldEtale_cohomology_eq_zero_of_tsen Ω t ht hfin S m hm0 hm n v

/-- Finite constant coefficients on the original geometric function field
have zero cohomology above degree one, without any characteristic-zero
assumption or a supplied cohomological annihilator. -/
theorem fieldEtale_constantFinite_cohomology_eq_zero_constantBaseChange
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap K F)) = ⊤)
    (A : AddCommGrpCat.{v}) [Finite A] (n : ℕ)
    (v : Sheaf.H.{v}
      ((constantSheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{v}).obj A)
      (n + 2)) : v = 0 := by
  obtain ⟨t, ht, hfin, -⟩ := exists_separatingParameter_constantBaseChange (k := k) hgen
  exact fieldEtale_constantFinite_cohomology_eq_zero_of_tsen Ω t ht hfin A n v

end EtaleCohomology

end AlgebraicCurve
