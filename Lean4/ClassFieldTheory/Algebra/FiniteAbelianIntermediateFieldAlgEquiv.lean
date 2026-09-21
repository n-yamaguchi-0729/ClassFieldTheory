import ClassFieldTheory.Algebra.IntermediateFieldAlgEquivOrderIso
import ClassFieldTheory.Algebra.AbelianGaloisEquiv

set_option autoImplicit false

/-!
# Finite abelian intermediate fields under an ambient algebra equivalence

An algebra equivalence of ambient fields transports finite-dimensionality and
the abelian Galois property of every intermediate field.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w

variable {F : Type u} {L : Type v} {L' : Type w}
  [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
  (e : L ≃ₐ[F] L') (E : IntermediateField F L)

/-- The equivalence of intermediate fields commutes with their base-field
embeddings. -/
theorem intermediateFieldMap_commutes :
    (algebraMap F (E.map e.toAlgHom)).comp (RingEquiv.refl F).toRingHom =
      (IntermediateField.intermediateFieldMap e E).toRingHom.comp
        (algebraMap F E) := by
  ext x
  simp

/-- Mapping an intermediate field through an ambient algebra equivalence
preserves its finite-dimensionality. -/
theorem finiteDimensional_intermediateField_map_algEquiv
    [FiniteDimensional F E] :
    FiniteDimensional F (E.map e.toAlgHom) := by
  exact Module.Finite.of_equiv_equiv
    (RingEquiv.refl F) (IntermediateField.intermediateFieldMap e E).toRingEquiv
    (intermediateFieldMap_commutes e E)

/-- Mapping an intermediate field through an ambient algebra equivalence
preserves its abelian Galois property. -/
theorem isAbelianGalois_intermediateField_map_algEquiv
    [IsAbelianGalois F E] :
    IsAbelianGalois F (E.map e.toAlgHom) := by
  exact isAbelianGalois_of_equiv_equiv
    (RingEquiv.refl F) (IntermediateField.intermediateFieldMap e E).toRingEquiv
    (intermediateFieldMap_commutes e E)

end ClassFieldTheory
