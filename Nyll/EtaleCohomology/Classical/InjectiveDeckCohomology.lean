/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.DeckSectionRepresentations
public import Nyll.EtaleCohomology.Classical.IntegralDeckSectionRepresentations
public import Nyll.EtaleCohomology.Classical.MappedCechPrimitives
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Higher deck cohomology of actual injective etale sheaves

The actual geometric Cech primitives and the proved standard-resolution
comparison imply vanishing for actual deck-section coefficients.
No injectivity of a restricted sheaf and no cohomology comparison is assumed.
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleCohomology

/-- Every positive-degree standard-resolution cocycle with coefficients
in sections of an actual injective etale sheaf has a primitive. -/
theorem exists_injective_integralStandardDeck_primitive
    (X : Scheme.{u}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (a : (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).X (n + 1) ⟶
      integralFiniteEtaleDeckSectionsRep X I Y)
    (ha : (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d (n + 2) (n + 1) ≫ a = 0) :
    ∃ b : (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).X n ⟶
        integralFiniteEtaleDeckSectionsRep X I Y,
      (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d (n + 1) n ≫ b = a := by
  let E := integralGeometricSectionStandardDeckHomAddEquiv X I Y
  let z : I.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 2) => Y))) :=
    (E (n + 1)).symm a
  have hz : integralGeometricSectionToStandardDeckHom X I Y (n + 1) z = a :=
    (E (n + 1)).apply_symm_apply a
  have hzδ : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      I.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y (n + 1) i)).op z = 0 := by
    apply (E (n + 2)).injective
    have hc := integralGeometricSectionToStandardDeckHom_d X I Y (n + 1) z
    have hzero : (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d (n + 2) (n + 1) ≫
        integralGeometricSectionToStandardDeckHom X I Y (n + 1) z = 0 := by
      rw [hz]
      exact ha
    exact hc.trans (hzero.trans (map_zero (E (n + 2))).symm)
  obtain ⟨b, hb⟩ := exists_injective_mappedGeometricCech_primitive
    (finiteEtaleInclusion X) X.smallEtaleTopology Y I n z hzδ
  refine ⟨integralGeometricSectionToStandardDeckHom X I Y n b, ?_⟩
  exact (integralGeometricSectionToStandardDeckHom_d X I Y n b).symm.trans
    ((congrArg (integralGeometricSectionToStandardDeckHom X I Y (n + 1)) hb).trans hz)

/-- The actual standard cochain complex of injective sheaf sections is
exact in every positive degree. -/
theorem injective_integralStandardDeckCochains_exactAt_succ
    (X : Scheme.{u}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    ((Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).linearYonedaObj (ULift.{u} ℤ)
      (integralFiniteEtaleDeckSectionsRep X I Y)).ExactAt (n + 1) := by
  let K := (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).linearYonedaObj (ULift.{u} ℤ)
    (integralFiniteEtaleDeckSectionsRep X I Y)
  apply (K.exactAt_iff' n (n + 1) (n + 2)
    ((ComplexShape.up ℕ).prev_eq'
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
    ((ComplexShape.up ℕ).next_eq'
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  change (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d (n + 2) (n + 1) ≫ a = 0 at ha
  exact exists_injective_integralStandardDeck_primitive X I Y n a ha

/-- The actual integral deck cohomology vanishes in every positive degree. -/
theorem isZero_integralCohomology_injective_deckSections_succ
    (X : Scheme.{u}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    IsZero (IntegralGroupCohomology.cohomology
      (finiteEtaleDeckSectionsRep X I Y) (n + 1)) := by
  have h : IsZero (groupCohomology (integralFiniteEtaleDeckSectionsRep X I Y) (n + 1)) :=
    (injective_integralStandardDeckCochains_exactAt_succ X I Y n).isZero_homology.of_iso
      (groupCohomologyIso (integralFiniteEtaleDeckSectionsRep X I Y) (n + 1)
        (Rep.standardResolution (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ))
  exact IntegralGroupCohomology.integerScalars.map_isZero h

/-- The same geometric primitive proves vanishing for the independent-universe owner. -/
theorem isZero_universeCohomology_injective_deckSections_succ
    (X : Scheme.{u}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    IsZero (IntegralGroupCohomology.Universe.cohomology
      (finiteEtaleDeckSectionsRep X I Y) (n + 1)) :=
  (isZero_integralCohomology_injective_deckSections_succ X I Y n).of_iso
    (IntegralGroupCohomology.Universe.cohomologyIsoCommon
      (finiteEtaleDeckSectionsRep X I Y) (n + 1))

/-- Every positive-degree standard-resolution cocycle with coefficients
in sections of an actual injective etale sheaf has a primitive. -/
theorem exists_injective_standardDeck_primitive
    (X : Scheme.{0}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{0}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (a : (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).X (n + 1) ⟶
      finiteEtaleDeckSectionsRep X I Y)
    (ha : (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).d (n + 2) (n + 1) ≫ a = 0) :
    ∃ b : (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).X n ⟶
        finiteEtaleDeckSectionsRep X I Y,
      (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).d (n + 1) n ≫ b = a := by
  let E := geometricSectionStandardDeckHomAddEquiv X I Y
  let z : I.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 2) => Y))) :=
    (E (n + 1)).symm a
  have hz : geometricSectionToStandardDeckHom X I Y (n + 1) z = a :=
    (E (n + 1)).apply_symm_apply a
  have hzδ : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      I.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y (n + 1) i)).op z = 0 := by
    apply (E (n + 2)).injective
    have hc := geometricSectionToStandardDeckHom_d X I Y (n + 1) z
    have hzero : (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).d (n + 2) (n + 1) ≫
        geometricSectionToStandardDeckHom X I Y (n + 1) z = 0 := by
      rw [hz]
      exact ha
    exact hc.trans (hzero.trans (map_zero (E (n + 2))).symm)
  obtain ⟨b, hb⟩ := exists_injective_mappedGeometricCech_primitive
    (finiteEtaleInclusion X) X.smallEtaleTopology Y I n z hzδ
  refine ⟨geometricSectionToStandardDeckHom X I Y n b, ?_⟩
  exact (geometricSectionToStandardDeckHom_d X I Y n b).symm.trans
    ((congrArg (geometricSectionToStandardDeckHom X I Y (n + 1)) hb).trans hz)

/-- The actual standard cochain complex of injective sheaf sections is
exact in every positive degree. -/
theorem injective_standardDeckCochains_exactAt_succ
    (X : Scheme.{0}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{0}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    ((Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).linearYonedaObj ℤ
      (finiteEtaleDeckSectionsRep X I Y)).ExactAt (n + 1) := by
  let K := (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).linearYonedaObj ℤ
    (finiteEtaleDeckSectionsRep X I Y)
  apply (K.exactAt_iff' n (n + 1) (n + 2)
    ((ComplexShape.up ℕ).prev_eq'
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
    ((ComplexShape.up ℕ).next_eq'
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  change (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).d (n + 2) (n + 1) ≫ a = 0 at ha
  exact exists_injective_standardDeck_primitive X I Y n a ha

/-- All positive-degree group cohomology of actual deck sections of
an injective etale sheaf vanishes, proved from actual geometric descent. -/
theorem isZero_groupCohomology_injective_deckSections_succ
    (X : Scheme.{0}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{0}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    IsZero (groupCohomology (finiteEtaleDeckSectionsRep X I Y) (n + 1)) :=
  (isZero_integralCohomology_injective_deckSections_succ X I Y n).of_iso
    (IntegralGroupCohomology.cohomologyIsoOriginal
      (finiteEtaleDeckSectionsRep X I Y) (n + 1)).symm

end EtaleCohomology
