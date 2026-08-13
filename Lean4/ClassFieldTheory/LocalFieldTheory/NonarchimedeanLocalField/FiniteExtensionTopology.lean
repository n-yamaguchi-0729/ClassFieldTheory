import LocalFieldTheory.NonarchimedeanLocalField.Basic
import LocalFieldTheory.NonarchimedeanLocalField.ValuedTopology
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Valuation.Extension

/-!
# The canonical topology on a finite extension of a local field

This file packages the spectral norm topology on a finite extension of a
nonarchimedean local field.  The definitions are deliberately explicit: they
let downstream constructions put several finite extensions in one diagram
while using the same topology on every field.
-/

noncomputable section

namespace LocalFieldTheory

open scoped NNReal ValuativeRel

/-- The normed-field structure canonically associated with the native
topology of a nonarchimedean local field. -/
@[reducible]
noncomputable def localFieldNontriviallyNormedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : NontriviallyNormedField K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valued K (ValuativeRel.ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  exact Valued.toNontriviallyNormedField
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

/-- The native norm obtained from a nonarchimedean local field is
ultrametric.  This is kept as a named companion to
`localFieldNontriviallyNormedField` so that every use of the spectral norm
starts from the same norm and the same ultrametric structure. -/
theorem localFieldIsUltrametricDist
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField K :=
      localFieldNontriviallyNormedField K
    IsUltrametricDist K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valued K (ValuativeRel.ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  infer_instance

/-- A finite extension, equipped with the spectral norm extending the native
topology of its nonarchimedean local base field. -/
@[reducible]
noncomputable def finiteExtensionSpectralNormedField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : NontriviallyNormedField L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  letI : CompleteSpace K := inferInstance
  exact spectralNorm.nontriviallyNormedField K L

/-- A finite extension is complete for its canonical spectral norm. -/
theorem finiteExtensionSpectralCompleteSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    CompleteSpace L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  letI : CompleteSpace K := inferInstance
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  exact spectralNorm.completeSpace K L

/-- A finite extension is locally compact for its canonical spectral norm. -/
theorem finiteExtensionSpectralLocallyCompactSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    LocallyCompactSpace L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  letI : CompleteSpace K := inferInstance
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  letI : NormedSpace K L := spectralNorm.normedSpace K L
  letI : CompleteSpace L := finiteExtensionSpectralCompleteSpace K L
  exact LocallyCompactSpace.of_finiteDimensional_of_complete K L

/-- The spectral norm on a finite extension of a nonarchimedean local field
is ultrametric. -/
theorem finiteExtensionSpectralIsUltrametricDist
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    IsUltrametricDist L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  exact
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := L) (x - y) (y - z)⟩

/-- The valuative relation induced by the canonical spectral norm. -/
@[reducible]
noncomputable def finiteExtensionSpectralValuativeRel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    ValuativeRel L := by
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  letI : IsUltrametricDist L :=
    finiteExtensionSpectralIsUltrametricDist K L
  letI : Valued L ℝ≥0 := NormedField.toValued
  exact ValuativeRel.ofValuation (Valued.v : Valuation L ℝ≥0)

/-- A finite extension with the spectral norm is again a nonarchimedean
local field. -/
theorem finiteExtensionSpectralIsNonarchimedeanLocalField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
    IsNonarchimedeanLocalField L := by
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  letI : CompleteSpace L := finiteExtensionSpectralCompleteSpace K L
  letI : LocallyCompactSpace L :=
    finiteExtensionSpectralLocallyCompactSpace K L
  letI : IsUltrametricDist L :=
    finiteExtensionSpectralIsUltrametricDist K L
  letI : Valued L ℝ≥0 := NormedField.toValued
  let vL : Valuation L ℝ≥0 := Valued.v
  letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
  letI : vL.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := L)).IsNontrivial)
  letI : vL.Compatible := Valuation.Compatible.ofValuation vL
  letI : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vL).2 inferInstance
  letI : IsValuativeTopology L :=
    isValuativeTopology_of_valued_ofValuation L ℝ≥0
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-- The valuative relation coming from the spectral norm is the canonical
extension of the native valuation on the local base field. -/
theorem finiteExtensionSpectralValuation_hasExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L) := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  letI : Valued K (ValuativeRel.ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  letI : IsUltrametricDist L :=
    finiteExtensionSpectralIsUltrametricDist K L
  letI : Valued L ℝ≥0 := NormedField.toValued
  let vL : Valuation L ℝ≥0 := Valued.v
  letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
  letI : vL.Compatible := Valuation.Compatible.ofValuation vL
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
    ValuativeRel.valuation K x ≤ 1
  rw [← (ValuativeRel.valuation L).vle_one_iff, vL.vle_one_iff]
  change spectralNorm K L (algebraMap K L x) ≤ 1 ↔
    ValuativeRel.valuation K x ≤ 1
  rw [spectralNorm_extends]
  exact Valued.toNormedField.norm_le_one_iff
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

/-- If `E/K` and `L/K` carry their canonical `K`-spectral norms in a
tower `K \to E \to L`, then the given `E`-algebra structure on `L` is a
normed algebra.  In particular, inclusion and norm maps in finite towers are
continuous for one topology on each field. -/
@[reducible]
noncomputable def finiteExtensionSpectralNormedAlgebra
    (K E L : Type) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    NormedAlgebra E L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  letI : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  exact
    { (inferInstance : Algebra E L) with
      norm_smul_le := by
        intro r x
        have hr : ‖algebraMap E L r‖ = ‖r‖ := by
          change spectralNorm K L (algebraMap E L r) =
            spectralNorm K E r
          exact (spectralNorm.eq_of_tower r).symm
        rw [Algebra.smul_def, norm_mul, hr] }

/-- In a finite tower equipped throughout with the spectral norms over its
local base, the upper spectral valuation extends the intermediate spectral
valuation. -/
theorem finiteExtensionSpectralValuation_hasExtension_of_tower
    (K E L : Type) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel E :=
      finiteExtensionSpectralValuativeRel K E
    letI : ValuativeRel L :=
      finiteExtensionSpectralValuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation E)
      (ValuativeRel.valuation L) := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  letI : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  letI : NontriviallyNormedField L :=
    finiteExtensionSpectralNormedField K L
  letI : NormedAlgebra E L :=
    finiteExtensionSpectralNormedAlgebra K E L
  letI : IsUltrametricDist E :=
    finiteExtensionSpectralIsUltrametricDist K E
  letI : IsUltrametricDist L :=
    finiteExtensionSpectralIsUltrametricDist K L
  letI : Valued E ℝ≥0 := NormedField.toValued
  letI : Valued L ℝ≥0 := NormedField.toValued
  let vE : Valuation E ℝ≥0 := Valued.v
  let vL : Valuation L ℝ≥0 := Valued.v
  letI : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  letI : ValuativeRel L :=
    finiteExtensionSpectralValuativeRel K L
  letI : vE.Compatible := Valuation.Compatible.ofValuation vE
  letI : vL.Compatible := Valuation.Compatible.ofValuation vL
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change
    ValuativeRel.valuation L (algebraMap E L x) ≤ 1 ↔
      ValuativeRel.valuation E x ≤ 1
  rw [← (ValuativeRel.valuation L).vle_one_iff, vL.vle_one_iff,
    ← (ValuativeRel.valuation E).vle_one_iff, vE.vle_one_iff]
  change
    spectralNorm K L (algebraMap E L x) ≤ 1 ↔
      spectralNorm K E x ≤ 1
  rw [(spectralNorm.eq_of_tower x).symm]

end LocalFieldTheory
