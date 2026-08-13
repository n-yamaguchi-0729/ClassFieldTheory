import AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import AlgebraicNumberTheory.Galois.NormalFieldRange
import AlgebraicNumberTheory.RayClass.Topology
import GlobalClassFieldTheory.GlobalClassFields.ConductorLattice
import GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
import GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity
import GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue

/-!
# Actual ray class fields

For a modulus `m` of a number field `K`, its ray congruence subgroup
`C_K^m` is closed and has finite index.  The finite-index class-field
construction therefore selects an actual finite abelian extension whose
determinant-norm range is exactly `C_K^m`.

The construction first occurs over the canonical fixed-field copy of `K`
inside the rational separable closure.  We then install the canonical
scalar structure from the original field, identify the norm range over
that original field, and obtain the genuine reciprocity equivalence

`Gal(K^m / K) ≃ C_K / C_K^m`.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open Reciprocity
open CyclicCohomology

variable {K : Type} [Field K] [NumberField K]

/-- The concrete finite Galois norm neighbourhood used to select the
ray class field attached to `m`. -/
noncomputable abbrev rayClassFieldNormAmbient
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) : Type :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The compatible abstract base subgroup used by the selected ray
class-field realization. -/
noncomputable abbrev rayClassFieldBaseSubgroup
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The finite abelian subextension selected by the ray congruence
subgroup `C_K^m`. -/
noncomputable abbrev rayClassFieldSubextension
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    FiniteAbelianSubextension
      (rayClassFieldBaseSubgroup K m) :=
  closedFiniteIndexClassFieldSubextension
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The canonical fixed-field copy of the original number field in the
selected ray class-field realization. -/
noncomputable abbrev rayClassFieldBase
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- A chosen finite ray-class-field realization attached to `m`, selected
inside the rational separable closure.  Its intrinsic realization in the
fixed separable closure of `K` is `rayClassFieldSubfield`. -/
noncomputable abbrev rayClassField
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) : Type :=
  closedFiniteIndexClassField
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The canonical equivalence from `K` to the fixed-field base of its
selected ray class field. -/
noncomputable abbrev rayClassFieldBaseEquiv
    (m : RayClass.Modulus K) :
    K ≃ₐ[ℚ] rayClassFieldBase K m :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The ray congruence subgroup transported to the fixed-field base of
the selected realization. -/
def rayClassFieldTransportedCongruenceSubgroup
    (m : RayClass.Modulus K) :
    Subgroup
      (IdeleClassGroup (rayClassFieldBase K m)) :=
  (RayClass.Modulus.congruenceSubgroup m).map
    (ideleClassCongr
      (rayClassFieldBaseEquiv (K := K) m)).toMonoidHom

/-- The determinant-norm range over the fixed-field base of the
selected ray class field is the transported ray congruence subgroup. -/
theorem rayClassField_ideleClassNorm_range
    (m : RayClass.Modulus K) :
    (_root_.ideleClassNorm
      (rayClassFieldBase K m)
      (rayClassField K m)).range =
      rayClassFieldTransportedCongruenceSubgroup
        (K := K) m := by
  simpa only [rayClassFieldTransportedCongruenceSubgroup,
    rayClassFieldBaseEquiv, rayClassField, rayClassFieldBase] using
    (closedFiniteIndexClassField_ideleClassNorm_range_over_base
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m))

/-- The fixed-field base of the selected ray class field, regarded as
an algebra over the original number field. -/
noncomputable abbrev rayClassFieldBaseAlgebraOverOriginal
    (m : RayClass.Modulus K) :
    Algebra K (rayClassFieldBase K m) :=
  closedFiniteIndexClassFieldBaseAlgebraOverOriginal
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The canonical fixed-field identification as an equivalence over
the original number field. -/
noncomputable abbrev rayClassFieldBaseEquivOverOriginal
    (m : RayClass.Modulus K) :
    K ≃ₐ[K] rayClassFieldBase K m :=
  closedFiniteIndexClassFieldBaseEquivOverOriginal
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The selected ray class field as an algebra over the original
number field. -/
noncomputable abbrev rayClassFieldAlgebraOverOriginal
    (m : RayClass.Modulus K) :
    Algebra K (rayClassField K m) :=
  closedFiniteIndexClassFieldAlgebraOverOriginal
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The scalar map into the ray class field is the canonical base
equivalence followed by fixed-field inclusion. -/
@[simp]
theorem rayClassField_algebraMap_original
    (m : RayClass.Modulus K) (x : K) :
    algebraMap K (rayClassField K m) x =
      algebraMap
        (rayClassFieldBase K m)
        (rayClassField K m)
        (rayClassFieldBaseEquiv (K := K) m x) := by
  simpa only [rayClassField, rayClassFieldBase,
    rayClassFieldBaseEquiv] using
    (closedFiniteIndexClassField_algebraMap_original
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m) x)

/-- A chosen embedding of the finite ray-class-field realization into the
fixed separable closure of its original base field. -/
noncomputable def rayClassFieldEmbedding
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    rayClassField K m →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

/-- The intrinsic ray class field as an intermediate field of the fixed
separable closure of `K`. -/
noncomputable def rayClassFieldSubfield
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    IntermediateField K (SeparableClosure K) :=
  (rayClassFieldEmbedding K m).fieldRange

/-- Every embedding of the chosen finite ray-class-field realization into
the fixed separable closure has the intrinsic ray-class-field range. -/
theorem rayClassFieldSubfield_eq_fieldRange
    (m : RayClass.Modulus K)
    (f : rayClassField K m →ₐ[K] SeparableClosure K) :
    rayClassFieldSubfield K m = f.fieldRange :=
  AlgHom.fieldRange_eq_of_normal
    (rayClassFieldEmbedding K m) f

/-- Over the original number field, the determinant-norm range of the
selected ray class field is exactly `C_K^m`. -/
theorem rayClassField_ideleClassNorm_range_over_original
    (m : RayClass.Modulus K) :
    (_root_.ideleClassNorm K (rayClassField K m)).range =
      RayClass.Modulus.congruenceSubgroup m := by
  simpa only [rayClassField] using
    (closedFiniteIndexClassField_ideleClassNorm_range
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m))

/-- A finite abelian extension is isomorphic over `K` to the selected
ray class field of modulus `m` exactly when its genuine idèle-class
norm range is `C_K^m`.  This is the actual-field uniqueness statement
for ray class fields. -/
theorem
    nonempty_algEquiv_rayClassField_iff_ideleClassNorm_range_eq
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (m : RayClass.Modulus K) :
    Nonempty (L ≃ₐ[K] rayClassField K m) ↔
      (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup m := by
  rw [
    nonempty_algEquiv_iff_ideleClassNorm_range_eq,
    rayClassField_ideleClassNorm_range_over_original]

/-- Increasing the modulus decreases the actual determinant-norm
range of the selected ray class field.  This is the norm-subgroup
form of the contravariant inclusion of ray class fields. -/
theorem rayClassField_ideleClassNorm_range_antitone
    {m n : RayClass.Modulus K}
    (hmn : m ≤ n) :
    (_root_.ideleClassNorm K (rayClassField K n)).range ≤
      (_root_.ideleClassNorm K (rayClassField K m)).range := by
  calc
    (_root_.ideleClassNorm K (rayClassField K n)).range =
        RayClass.Modulus.congruenceSubgroup n :=
      rayClassField_ideleClassNorm_range_over_original
        (K := K) n
    _ ≤ RayClass.Modulus.congruenceSubgroup m :=
      rayClassCongruenceSubgroup_antitone
        (K := K) hmn
    _ = (_root_.ideleClassNorm K (rayClassField K m)).range :=
      (rayClassField_ideleClassNorm_range_over_original
        (K := K) m).symm

/-- Divisibility of moduli produces an embedding between the selected
ray-class-field types over the original number field.  Literal containment
inside the fixed separable closure is instead stated by
`rayClassFieldSubfield_mono`. -/
theorem rayClassField_nonempty_algHom_of_le
    {m n : RayClass.Modulus K}
    (hmn : m ≤ n) :
    Nonempty
      (rayClassField K m →ₐ[K]
        rayClassField K n) :=
  finiteAbelianExtension_nonempty_algHom_of_normRange_le
    (K := K)
    (rayClassField K m)
    (rayClassField K n)
    (rayClassField_ideleClassNorm_range_antitone
      (K := K) hmn)

/-- Divisibility of moduli gives literal inclusion of the corresponding
intrinsic ray class fields inside the fixed separable closure. -/
theorem rayClassFieldSubfield_mono
    {m n : RayClass.Modulus K}
    (hmn : m ≤ n) :
    rayClassFieldSubfield K m ≤ rayClassFieldSubfield K n := by
  let f : rayClassField K m →ₐ[K] rayClassField K n :=
    Classical.choice
      (rayClassField_nonempty_algHom_of_le (K := K) hmn)
  calc
    rayClassFieldSubfield K m =
        ((rayClassFieldEmbedding K n).comp f).fieldRange :=
      rayClassFieldSubfield_eq_fieldRange
        (K := K) m ((rayClassFieldEmbedding K n).comp f)
    _ ≤ (rayClassFieldEmbedding K n).fieldRange := by
      intro x hx
      rcases AlgHom.mem_fieldRange.mp hx with ⟨y, rfl⟩
      exact AlgHom.mem_fieldRange.mpr ⟨f y, rfl⟩
    _ = rayClassFieldSubfield K n := rfl

/-- A finite abelian extension embeds in the selected ray class field
of modulus `m` exactly when `m` is a defining modulus for its genuine
idèle-class norm subgroup. -/
theorem
    nonempty_algHom_to_rayClassField_iff_isDefiningModulus
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (m : RayClass.Modulus K) :
    Nonempty (L →ₐ[K] rayClassField K m) ↔
      IsDefiningModulus
        ((_root_.ideleClassNorm K L).range) m := by
  change
    Nonempty (L →ₐ[K] rayClassField K m) ↔
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range
  rw [
    nonempty_algHom_iff_ideleClassNorm_range_le,
    rayClassField_ideleClassNorm_range_over_original]

/-- Actual containment in a narrow ray class field is equivalent to
divisibility by the exact narrow finite conductor. -/
theorem
    nonempty_algHom_to_rayClassField_narrowOfFinite_iff_narrowFiniteConductor_le
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (n : RayClass.FiniteModulus K) :
    Nonempty
        (L →ₐ[K]
          rayClassField K (RayClass.Modulus.narrowOfFinite n)) ↔
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) ≤ n := by
  rw [nonempty_algHom_to_rayClassField_iff_isDefiningModulus]
  constructor
  · intro hm
    simpa only [ideleClassNormNarrowFiniteConductor,
      RayClass.Modulus.finitePart_narrowOfFinite] using
      (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).narrowFiniteConductor_le hm
  · intro hn
    exact
      isDefiningModulus_mono
        ((_root_.ideleClassNorm K L).range)
        (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
          (K := K) (L := L))
        ⟨hn, Finset.subset_univ _⟩

/-- The ray class field of the exact narrow finite conductor genuinely
contains the given finite abelian extension. -/
theorem
    finiteAbelianExtension_nonempty_algHom_to_conductorRayClassField
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    Nonempty
      (L →ₐ[K]
        rayClassField K
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) :=
  (nonempty_algHom_to_rayClassField_iff_isDefiningModulus
    (K := K) L
    (RayClass.Modulus.narrowOfFinite
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)))).2
    (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
      (K := K) (L := L))

/-- Every finite abelian extension is genuinely contained in a ray
class field over the original base. -/
theorem finiteAbelianExtension_exists_rayClassFieldEmbedding
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    ∃ m : RayClass.Modulus K,
      Nonempty (L →ₐ[K] rayClassField K m) :=
  ⟨RayClass.Modulus.narrowOfFinite
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)),
    finiteAbelianExtension_nonempty_algHom_to_conductorRayClassField
      (K := K) L⟩

/-- The exact narrow finite conductor is the greatest common divisor
of the finite parts of the moduli of the actual ray class fields
containing a finite abelian extension. -/
theorem
    ideleClassNorm_narrowFiniteConductor_is_gcd_of_rayClassField_embeddings
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    (∀ m : RayClass.Modulus K,
        Nonempty (L →ₐ[K] rayClassField K m) →
          ideleClassNormNarrowFiniteConductor
              (K := K) (L := L) ≤ m.finitePart) ∧
      (∀ d : RayClass.FiniteModulus K,
        (∀ m : RayClass.Modulus K,
          Nonempty (L →ₐ[K] rayClassField K m) →
            d ≤ m.finitePart) →
          d ≤ ideleClassNormNarrowFiniteConductor
            (K := K) (L := L)) := by
  have hgcd :=
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor_is_gcd
  constructor
  · intro m hm
    simpa only [ideleClassNormNarrowFiniteConductor] using
      hgcd.1 m
        ((nonempty_algHom_to_rayClassField_iff_isDefiningModulus
          (K := K) L m).1 hm)
  · intro d hd
    simpa only [ideleClassNormNarrowFiniteConductor] using
      hgcd.2 d (fun m hm =>
        hd m
          ((nonempty_algHom_to_rayClassField_iff_isDefiningModulus
            (K := K) L m).2 hm))

/-- Global reciprocity for the selected ray class field as a
homeomorphic multiplicative equivalence

`Gal(K^m / K) ≃ₜ* C_K / C_K^m`.

The topology is the genuine finite Krull topology on the Galois group
and the native quotient topology on the ray class group. -/
noncomputable def
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃ₜ*
      RayClass.RayClassGroup m := by
  letI : DiscreteTopology (RayClass.RayClassGroup m) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup m)
  exact
    { closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) (RayClass.Modulus.congruenceSubgroup m)
        (RayClass.isClosed_congruenceSubgroup m) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The underlying map of topological ray-class reciprocity is the
general closed-finite-index reciprocity equivalence. -/
@[simp]
theorem
    rayClassFieldGaloisContinuousMulEquivRayClassGroup_apply
    (m : RayClass.Modulus K)
    (σ : Gal((rayClassField K m) / K)) :
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m σ =
      closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) (RayClass.Modulus.congruenceSubgroup m)
        (RayClass.isClosed_congruenceSubgroup m) σ := by
  rfl

/-- On an idèle-class representative, topological ray-class
reciprocity sends its genuine global norm-residue symbol to its ray
class modulo `C_K^m`. -/
@[simp]
theorem
    rayClassFieldGaloisContinuousMulEquivRayClassGroup_globalNormResidue
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m
        (Reciprocity.globalNormResidueMonoidHom
          K (rayClassField K m) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c := by
  rw [rayClassFieldGaloisContinuousMulEquivRayClassGroup_apply]
  simpa only [rayClassField] using
    (closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m) c)

/-- The degree of the selected ray class field is the order of the ray
class group. -/
theorem rayClassField_finrank_eq_rayClassGroup_card
    (m : RayClass.Modulus K) :
    Module.finrank K (rayClassField K m) =
      Nat.card (RayClass.RayClassGroup m) := by
  calc
    Module.finrank K (rayClassField K m) =
        (RayClass.Modulus.congruenceSubgroup m).index :=
      by
        simpa only [rayClassField] using
          (closedFiniteIndexClassField_finrank_eq_index
            (K := K) (RayClass.Modulus.congruenceSubgroup m)
            (RayClass.isClosed_congruenceSubgroup m))
    _ =
        Nat.card
          (IdeleClassGroup K ⧸
            RayClass.Modulus.congruenceSubgroup m) :=
      Subgroup.index_eq_card
        (RayClass.Modulus.congruenceSubgroup m)
    _ =
        Nat.card (RayClass.RayClassGroup m) :=
      rfl

/-- Global reciprocity identifies the genuine Galois group of the
selected ray class field with the ray class group `C_K / C_K^m`. -/
noncomputable abbrev rayClassFieldGaloisEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃*
      RayClass.RayClassGroup m :=
  closedFiniteIndexClassFieldGaloisEquivNormQuotient
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- Under ray-class reciprocity, the actual global norm-residue symbol
is the ray class of its idèle-class representative. -/
@[simp]
theorem rayClassFieldGaloisEquivRayClassGroup_globalNormResidue
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    rayClassFieldGaloisEquivRayClassGroup
        (K := K) m
        (globalNormResidueMonoidHom K
          (rayClassField K m) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c := by
  simpa only [rayClassField, rayClassFieldGaloisEquivRayClassGroup] using
    (closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m) c)

end GlobalClassFields
end GlobalClassFieldTheory
