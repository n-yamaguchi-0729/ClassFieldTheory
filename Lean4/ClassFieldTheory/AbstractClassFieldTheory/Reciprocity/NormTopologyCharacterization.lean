import AbstractClassFieldTheory.Reciprocity.Main
import AbstractClassFieldTheory.Reciprocity.ValuationContinuity
import AbstractClassFieldTheory.Reciprocity.NormContinuity
import CyclicCohomology.IntegralRepUniverse

/-!
# The norm-topology characterization

This file supplies part (i), whose finite-index assertion uses the actual
reciprocity isomorphism of the abstract reciprocity theorem.  Parts (ii)--(iv) are proved in the
imported valuation-, norm-, and norm-topology modules.
-/

noncomputable section

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The norm-subgroup basis characterization: in the norm topology, the open subgroups are
exactly the closed subgroups of finite index.  Finiteness of every defining
norm quotient is obtained from the abstract reciprocity theorem, not assumed. -/
theorem normTopology_open_iff_closed_finiteIndex
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : ClosedSubgroup G)
    [hKabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K H ↔
      IsNormClosed A K H ∧
        Finite (ambientFixedAddSubgroup A K ⧸ H) := by
  apply normTopology_open_iff_closed_finiteIndex_of_finite_normQuotients
    A K _ H
  intro L
  let KF : FiniteAbstractField G := ⟨K, hKabsolute⟩
  letI : (extensionSubgroup K L.field L.below).Normal := L.normal
  letI : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) := L.finite
  letI : Finite (Abelianization L.extensionQuotient) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  change Finite (FiniteNormQuotient A K L.field L.below)
  exact Finite.of_equiv
    (Additive (Abelianization L.extensionQuotient))
    (D.abstractReciprocityEquiv A v hcf KF L).toEquiv

end ValuationData
end ClassFormation
