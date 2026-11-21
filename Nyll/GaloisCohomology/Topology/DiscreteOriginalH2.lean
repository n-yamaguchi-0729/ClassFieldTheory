/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.H2EquivariantEquivalence
public import Nyll.GaloisCohomology.Topology.DiscreteGroupH2

/-! # Original integer cohomology of a discrete representation -/

@[expose] public section

open CategoryTheory

noncomputable section
namespace ContinuousCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
  (X : TopRep.{0} ℤ G)

/-- The actual continuous class identifies with its original integer class,
through dehomogenization and the identity on the coefficient carrier. -/
def discreteOriginalH2Equiv : continuousCohomology 2 X ≃+
    groupCohomology (underlyingIntegerRep X) 2 :=
  (discreteIntegralH2Equiv X).trans (groupCohomology.equivariantH2AddEquiv
    (A := underlyingIntegralRep X) (B := underlyingIntegerRep X)
    (MulEquiv.refl G) (AddEquiv.refl X) (fun _ _ => rfl))

/-- The comparison sends each representative to its original dehomogenization. -/
theorem discreteOriginalH2Equiv_π (z : cocycles X 2) :
    discreteOriginalH2Equiv X (π X 2 z) =
      groupCohomology.H2π (underlyingIntegerRep X) (dehomogenizeTwoOriginal X z) := by
  let f : underlyingIntegralRep X ≃+ underlyingIntegerRep X := AddEquiv.refl X
  let e := groupCohomology.equivariantH2AddEquiv (MulEquiv.refl G) f (fun _ _ => rfl)
  change e (discreteIntegralH2Hom X (π X 2 z)) = _
  rw [discreteIntegralH2Hom_π]
  refine (groupCohomology.equivariantH2AddEquiv_H2π
    (MulEquiv.refl G) f (fun _ _ => rfl) (dehomogenizeIntegralTwo X z)).trans ?_
  apply congrArg (groupCohomology.H2π (underlyingIntegerRep X))
  apply groupCohomology.cocycles₂_ext
  intro g h
  rfl

end ContinuousCohomology
