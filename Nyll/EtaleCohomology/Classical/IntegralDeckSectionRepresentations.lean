/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.DeckSectionRepresentations
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Abelian.Ext

/-!
# Integral standard cochains of actual deck sections

Lifted integer scalars put the existing standard resolution in the scheme's
universe. Coefficient transport leaves the actual section carrier, opposite
deck action, face restrictions and integer alternating differential unchanged.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open scoped Simplicial

namespace EtaleCohomology

/-- The existing deck representation transported along the actual integer ring equivalence. -/
abbrev integralFiniteEtaleDeckSectionsRep (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Y : FiniteEtale X) :
    Rep.{u} (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ :=
  (IntegralGroupCohomology.coefficientFunctor (Aut Y)ᵐᵒᵖ).obj
    (finiteEtaleDeckSectionsRep X F Y)

/-- An actual geometric Cech section defines a morphism from the
standard resolution, by linear extension of homogeneous deck evaluation. -/
def integralGeometricSectionToStandardDeckHom (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) :
    (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).X n ⟶ integralFiniteEtaleDeckSectionsRep X F Y :=
  Rep.ofHom
    { toLinearMap := (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n z)) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv (ULift.{u} ℤ)).toLinearMap
      isIntertwining' σ := by
        apply MonoidAlgebra.lhom_ext'
        intro g
        change Fin (n + 1) → (Aut Y)ᵐᵒᵖ at g
        apply LinearMap.ext_ring
        change (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n z))
            ((Representation.linearize (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ
              ((classifyingSpaceUniversalCover (Aut Y)ᵐᵒᵖ).obj (op ⦋n⦌))
              σ (MonoidAlgebra.single g (1 : ULift.{u} ℤ))).coeff) =
          (integralFiniteEtaleDeckSectionsRep X F Y).ρ σ
            ((Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n z))
              (Finsupp.single g (1 : ULift.{u} ℤ)))
        erw [Representation.linearize_single, MonoidAlgebra.coeff_single]
        change (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n z))
            (Finsupp.single (fun i => σ * g i) (1 : ULift.{u} ℤ)) =
          (integralFiniteEtaleDeckSectionsRep X F Y).ρ σ
            ((Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n z))
              (Finsupp.single g (1 : ULift.{u} ℤ)))
        erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
          one_smul, one_smul]
        exact homogeneousDeckSection_equivariant X F Y n z σ g }

/-- The standard-resolution morphism evaluates a basis tuple by
actual geometric restriction. -/
theorem integralGeometricSectionToStandardDeckHom_single
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) :
    (integralGeometricSectionToStandardDeckHom X F Y n z).hom
        (MonoidAlgebra.single g (1 : ULift.{u} ℤ)) =
      homogeneousDeckSection X F Y n z g := by
  change (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n z))
    (Finsupp.single g (1 : ULift.{u} ℤ)) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- Basis evaluation of a standard-resolution morphism has exactly the
actual homogeneous deck equivariance. -/
theorem integralStandardDeckHom_equivariant
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ)
    (a : (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).X n ⟶
      integralFiniteEtaleDeckSectionsRep X F Y)
    (σ : (Aut Y)ᵐᵒᵖ) (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) :
    a.hom (MonoidAlgebra.single (fun i => σ * g i) (1 : ULift.{u} ℤ)) =
      (integralFiniteEtaleDeckSectionsRep X F Y).ρ σ
        (a.hom (MonoidAlgebra.single g (1 : ULift.{u} ℤ))) := by
  have h := Rep.hom_comm_apply a σ (MonoidAlgebra.single g (1 : ULift.{u} ℤ))
  change a.hom (Representation.linearize (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ
    ((classifyingSpaceUniversalCover (Aut Y)ᵐᵒᵖ).obj (op ⦋n⦌))
      σ (MonoidAlgebra.single g (1 : ULift.{u} ℤ))) = _ at h
  erw [Representation.linearize_single] at h
  exact h

/-- The actual geometric construction gives every standard-resolution
cochain, uniquely. -/
theorem integralGeometricSectionToStandardDeckHom_bijective
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    Function.Bijective (integralGeometricSectionToStandardDeckHom X F Y n) := by
  constructor
  · intro s t h
    apply homogeneousDeckSection_injective X F Y n
    funext g
    exact (integralGeometricSectionToStandardDeckHom_single X F Y n s g).symm.trans
      ((congrArg (fun a => a.hom (MonoidAlgebra.single g (1 : ULift.{u} ℤ))) h).trans
        (integralGeometricSectionToStandardDeckHom_single X F Y n t g))
  · intro a
    obtain ⟨z, hz⟩ := exists_homogeneousDeckSection X F Y n
      (fun g => a.hom (MonoidAlgebra.single g (1 : ULift.{u} ℤ)))
      (integralStandardDeckHom_equivariant X F Y n a)
    refine ⟨z, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro g
    change Fin (n + 1) → (Aut Y)ᵐᵒᵖ at g
    apply LinearMap.ext_ring
    exact (integralGeometricSectionToStandardDeckHom_single X F Y n z g).trans (congrFun hz g)

/-- Actual geometric Cech sections and standard-resolution cochains
are additively equivalent in every degree. -/
def integralGeometricSectionStandardDeckHomAddEquiv
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))) ≃+
        ((Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).X n ⟶
          integralFiniteEtaleDeckSectionsRep X F Y) where
  toEquiv := Equiv.ofBijective (integralGeometricSectionToStandardDeckHom X F Y n)
    (integralGeometricSectionToStandardDeckHom_bijective X F Y n)
  map_add' s t := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro g
    change Fin (n + 1) → (Aut Y)ᵐᵒᵖ at g
    apply LinearMap.ext_ring
    change (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n (s + t)))
        (Finsupp.single g (1 : ULift.{u} ℤ)) =
      (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n s))
        (Finsupp.single g (1 : ULift.{u} ℤ)) +
      (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n t))
        (Finsupp.single g (1 : ULift.{u} ℤ))
    erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, one_smul, one_smul, one_smul]
    exact (F.obj.map ((finiteEtaleInclusion X).map
      (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom)).op).hom.map_add s t

/-- Evaluation on a basis tuple with an arbitrary integer coefficient. -/
theorem integralGeometricSectionToStandardDeckHom_single_coeff
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) (c : ULift.{u} ℤ) :
    (integralGeometricSectionToStandardDeckHom X F Y n z).hom (MonoidAlgebra.single g c) =
      c.down • homogeneousDeckSection X F Y n z g := by
  change (Finsupp.linearCombination (ULift.{u} ℤ) (homogeneousDeckSection X F Y n z))
    (Finsupp.single g c) = _
  exact Finsupp.linearCombination_single (ULift.{u} ℤ) c g

/-- The geometric-to-standard comparison intertwines the actual
alternating Cech differential with the standard group-resolution differential. -/
theorem integralGeometricSectionToStandardDeckHom_d
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) :
    integralGeometricSectionToStandardDeckHom X F Y (n + 1)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z) =
      (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d (n + 1) n ≫
        integralGeometricSectionToStandardDeckHom X F Y n z := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  change (integralGeometricSectionToStandardDeckHom X F Y (n + 1) _).hom
      (MonoidAlgebra.single g (1 : ULift.{u} ℤ)) =
    (integralGeometricSectionToStandardDeckHom X F Y n z).hom
      (((Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d (n + 1) n).hom
        (MonoidAlgebra.single g (1 : ULift.{u} ℤ)))
  erw [integralGeometricSectionToStandardDeckHom_single,
    Rep.standardComplex.d_apply, Rep.standardComplex.d_of, map_sum]
  change F.obj.map ((finiteEtaleInclusion X).map
      (Pi.lift fun j => (MulOpposite.unop (g j)).asIso.hom)).op
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z) =
    ∑ i : Fin (n + 2), (integralGeometricSectionToStandardDeckHom X F Y n z).hom
      (MonoidAlgebra.single (g ∘ i.succAbove) ((-1 : ULift.{u} ℤ) ^ (i : ℕ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integralGeometricSectionToStandardDeckHom_single_coeff]
  have hsign : (((-1 : ULift.{u} ℤ) ^ (i : ℕ)).down) = (-1 : ℤ) ^ (i : ℕ) :=
    map_pow (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) (-1) (i : ℕ)
  rw [hsign]
  exact congrArg (fun a => ((-1 : ℤ) ^ (i : ℕ)) • a)
    (homogeneousDeckSection_face X F Y n i z g)

/-- Changing coefficients commutes with the actual geometric-to-standard map. -/
theorem integralGeometricSectionToStandardDeckHom_naturality
    (X : Scheme.{u}) [ConnectedSpace X]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G)
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) :
    integralGeometricSectionToStandardDeckHom X G Y n
        (η.hom.app (op ((finiteEtaleInclusion X).obj
          (∏ᶜ fun _ : Fin (n + 1) => Y))) z) =
      integralGeometricSectionToStandardDeckHom X F Y n z ≫
        (IntegralGroupCohomology.coefficientFunctor (Aut Y)ᵐᵒᵖ).map
          (finiteEtaleDeckSectionsRepMap X Y η) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  change Fin (n + 1) → (Aut Y)ᵐᵒᵖ at g
  apply LinearMap.ext_ring
  change (integralGeometricSectionToStandardDeckHom X G Y n _).hom
      (MonoidAlgebra.single g (1 : ULift.{u} ℤ)) =
    (η.hom.app (op ((finiteEtaleInclusion X).obj Y)))
      ((integralGeometricSectionToStandardDeckHom X F Y n z).hom
        (MonoidAlgebra.single g (1 : ULift.{u} ℤ)))
  erw [integralGeometricSectionToStandardDeckHom_single,
    integralGeometricSectionToStandardDeckHom_single]
  exact (ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (η.hom.naturality ((finiteEtaleInclusion X).map
      (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom)).op) z).symm

/-- In universe zero every integer-weighted basis tuple has exactly the
value of the original literal-integer standard cochain. -/
theorem integralGeometricSectionToStandardDeckHom_single_original
    (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) (c : ℤ) :
    (integralGeometricSectionToStandardDeckHom X F Y n z).hom
        (MonoidAlgebra.single g (ULift.up c)) =
      (geometricSectionToStandardDeckHom X F Y n z).hom
        (MonoidAlgebra.single g c) := by
  rw [integralGeometricSectionToStandardDeckHom_single_coeff,
    geometricSectionToStandardDeckHom_single_coeff]

/-- The geometric differential is the alternating sum of the actual face restrictions. -/
def geometricDeckSectionDifferential (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Y : FiniteEtale X) (n : ℕ) :
    F.obj.obj (op ((finiteEtaleInclusion X).obj
        (∏ᶜ fun _ : Fin (n + 1) => Y))) ⟶
      F.obj.obj (op ((finiteEtaleInclusion X).obj
        (∏ᶜ fun _ : Fin (n + 2) => Y))) :=
  AddCommGrpCat.ofHom (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    (F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op).hom)

/-- Evaluation retains the original geometric alternating sum. -/
theorem geometricDeckSectionDifferential_apply (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) :
    geometricDeckSectionDifferential X F Y n z =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z := by
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    (F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op).hom) z = _
  rw [AddMonoidHom.finsetSum_apply]
  rfl

/-- Consecutive geometric differentials compose to zero, as witnessed by
the injective actual standard-cochain comparison. -/
theorem geometricDeckSectionDifferential_comp (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    geometricDeckSectionDifferential X F Y n ≫
      geometricDeckSectionDifferential X F Y (n + 1) = 0 := by
  ext z
  change geometricDeckSectionDifferential X F Y (n + 1)
    (geometricDeckSectionDifferential X F Y n z) = 0
  apply (integralGeometricSectionStandardDeckHomAddEquiv X F Y (n + 2)).injective
  rw [map_zero]
  change integralGeometricSectionToStandardDeckHom X F Y (n + 2)
      (geometricDeckSectionDifferential X F Y (n + 1)
        (geometricDeckSectionDifferential X F Y n z)) = 0
  rw [geometricDeckSectionDifferential_apply, integralGeometricSectionToStandardDeckHom_d,
    geometricDeckSectionDifferential_apply, integralGeometricSectionToStandardDeckHom_d,
    ← Category.assoc, (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d_comp_d, zero_comp]

/-- Actual geometric sections with their original alternating face differential. -/
def geometricDeckSectionCochains (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of
    (fun n => F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (geometricDeckSectionDifferential X F Y)
    (geometricDeckSectionDifferential_comp X F Y)

/-- The bundled complex has the same geometric differential. -/
theorem geometricDeckSectionCochains_d (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    (geometricDeckSectionCochains X F Y).d n (n + 1) =
      geometricDeckSectionDifferential X F Y n :=
  CochainComplex.of_d
    (fun k => F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (k + 1) => Y))))
    (geometricDeckSectionDifferential X F Y) n

/-- The degreewise geometric comparison is an actual isomorphism of
cochain complexes with the native integral standard resolution. -/
def integralGeometricDeckCochainIso (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] :
    geometricDeckSectionCochains X F Y ≅
      ((forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        ((Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).linearYonedaObj (ULift.{u} ℤ)
          (integralFiniteEtaleDeckSectionsRep X F Y)) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (integralGeometricSectionStandardDeckHomAddEquiv X F Y n).toAddCommGrpIso) ?_
  intro i j hij
  change i + 1 = j at hij
  subst j
  ext z
  change F.obj.obj (op ((finiteEtaleInclusion X).obj
    (∏ᶜ fun _ : Fin (i + 1) => Y))) at z
  change (Rep.standardComplex (ULift.{u} ℤ) (Aut Y)ᵐᵒᵖ).d (i + 1) i ≫
      integralGeometricSectionToStandardDeckHom X F Y i z =
    integralGeometricSectionToStandardDeckHom X F Y (i + 1)
      ((geometricDeckSectionCochains X F Y).d i (i + 1) z)
  rw [geometricDeckSectionCochains_d]
  exact (integralGeometricSectionToStandardDeckHom_d X F Y i z).symm.trans
    (congrArg (integralGeometricSectionToStandardDeckHom X F Y (i + 1))
      (geometricDeckSectionDifferential_apply X F Y i z).symm)

end EtaleCohomology
