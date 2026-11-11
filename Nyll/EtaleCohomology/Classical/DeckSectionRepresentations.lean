/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldGaloisAction
public import Nyll.EtaleCohomology.Classical.RepresentableCechTerms
public import Nyll.EtaleCohomology.Sites.GaloisPowerSections
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Actual opposite-deck section representations

The established contravariant deck action is bundled as an integer-linear
representation. The same coefficients occur in the actual geometric
Cech complex and the standard group-cohomology resolution.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open scoped Simplicial

namespace EtaleCohomology

/-- The actual representation of the opposite deck group on abelian
sheaf sections over a finite etale object. -/
def finiteEtaleDeckSectionsRep (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Y : FiniteEtale X) :
    Rep.{u} ℤ (Aut Y)ᵐᵒᵖ :=
  Rep.of
    { toFun := fun σ => ((finiteEtaleSheafDeckAction X F Y σ).asIso.hom).hom.toIntLinearMap
      map_one' := by
        apply LinearMap.ext
        intro s
        change (finiteEtaleSheafDeckAction X F Y 1).asIso.hom s = s
        rw [map_one]
        rfl
      map_mul' σ τ := by
        apply LinearMap.ext
        intro s
        exact congrArg (fun a => a.asIso.hom s) (map_mul (finiteEtaleSheafDeckAction X F Y) σ τ) }

/-- The bundled representation acts by actual geometric pullback. -/
theorem finiteEtaleDeckSectionsRep_apply (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Y : FiniteEtale X)
    (σ : (Aut Y)ᵐᵒᵖ)
    (s : F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) :
    (finiteEtaleDeckSectionsRep X F Y).ρ σ s =
      F.obj.map ((finiteEtaleInclusion X).map (MulOpposite.unop σ).asIso.hom).op s := rfl

/-- Actual coefficient morphisms induce equivariant maps of deck
section representations. -/
def finiteEtaleDeckSectionsRepMap (X : Scheme.{u}) (Y : FiniteEtale X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G) :
    finiteEtaleDeckSectionsRep X F Y ⟶ finiteEtaleDeckSectionsRep X G Y :=
  Rep.ofHom
    ⟨(η.hom.app (op ((finiteEtaleInclusion X).obj Y))).hom.toIntLinearMap,
      fun σ => by
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
          (η.hom.naturality
            ((finiteEtaleInclusion X).map (MulOpposite.unop σ).asIso.hom).op) s⟩

/-- Evaluation of an actual geometric section on a tuple of actual
deck transformations, in homogeneous coordinates. -/
def homogeneousDeckSection (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) :
    F.obj.obj (op ((finiteEtaleInclusion X).obj Y)) :=
  F.obj.map ((finiteEtaleInclusion X).map
    (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom)).op z

/-- Homogeneous geometric evaluation is equivariant for the actual
opposite-deck action, as required by the standard group resolution. -/
theorem homogeneousDeckSection_equivariant (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (σ : (Aut Y)ᵐᵒᵖ) (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) :
    homogeneousDeckSection X F Y n z (fun i => σ * g i) =
      (finiteEtaleDeckSectionsRep X F Y).ρ σ
        (homogeneousDeckSection X F Y n z g) := by
  have hg :
      (Pi.lift fun i => (MulOpposite.unop (σ * g i)).asIso.hom) =
        (MulOpposite.unop σ).asIso.hom ≫
          (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom) := by
    apply Pi.hom_ext
    intro i
    rw [Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π]
    rfl
  change F.obj.map ((finiteEtaleInclusion X).map
      (Pi.lift fun i => (MulOpposite.unop (σ * g i)).asIso.hom)).op z =
    F.obj.map ((finiteEtaleInclusion X).map (MulOpposite.unop σ).asIso.hom).op
      (F.obj.map ((finiteEtaleInclusion X).map
        (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom)).op z)
  rw [hg, Functor.map_comp, op_comp, F.obj.map_comp]
  rfl

/-- Homogeneous evaluation at a tuple with first coordinate one is
the established actual deck-coordinate equivalence. -/
theorem homogeneousDeckSection_normalized (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) (σ : Fin n → Aut Y) :
    homogeneousDeckSection X F Y n z (Fin.cases 1 (fun i => MulOpposite.op (σ i))) =
      galoisPowerSectionsAddEquiv X F Y n z σ := by
  let g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ := Fin.cases 1 (fun i => MulOpposite.op (σ i))
  have hg : (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom) =
      galoisPowerGraph Y n σ := by
    apply Pi.hom_ext
    intro i
    dsimp only [galoisPowerGraph]
    erw [Pi.lift_comp_π, Pi.lift_comp_π]
    exact Fin.cases rfl (fun _ => rfl) i
  change F.obj.map ((finiteEtaleInclusion X).map
    (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom)).op z = _
  rw [hg, galoisPowerSectionsAddEquiv_apply]

/-- Actual geometric sections are determined by homogeneous deck
coordinates. -/
theorem homogeneousDeckSection_injective (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    Function.Injective (homogeneousDeckSection X F Y n) := by
  intro s t h
  let E := galoisPowerSectionsAddEquiv X F Y n
  have he : E s = E t := by
    funext σ
    have hs := homogeneousDeckSection_normalized X F Y n s σ
    have ht := homogeneousDeckSection_normalized X F Y n t σ
    have hm := congrFun h (Fin.cases 1 (fun i => MulOpposite.op (σ i)))
    exact hs.symm.trans (hm.trans ht)
  exact E.injective he

/-- Every equivariant homogeneous cochain is represented by an
actual geometric section, using the proved deck decomposition. -/
theorem exists_homogeneousDeckSection (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (f : (Fin (n + 1) → (Aut Y)ᵐᵒᵖ) →
      F.obj.obj (op ((finiteEtaleInclusion X).obj Y)))
    (hf : ∀ (σ : (Aut Y)ᵐᵒᵖ) (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ),
      f (fun i => σ * g i) = (finiteEtaleDeckSectionsRep X F Y).ρ σ (f g)) :
    ∃ z, homogeneousDeckSection X F Y n z = f := by
  let c : (Fin n → Aut Y) → F.obj.obj (op ((finiteEtaleInclusion X).obj Y)) :=
    fun σ => f (Fin.cases 1 (fun i => MulOpposite.op (σ i)))
  let z := (galoisPowerSectionsAddEquiv X F Y n).symm c
  refine ⟨z, ?_⟩
  funext g
  let σ : Fin n → Aut Y := fun i => MulOpposite.unop ((g 0)⁻¹ * g i.succ)
  let v : Fin (n + 1) → (Aut Y)ᵐᵒᵖ := Fin.cases 1 (fun i => MulOpposite.op (σ i))
  have hv : homogeneousDeckSection X F Y n z v = f v := by
    rw [homogeneousDeckSection_normalized]
    exact congrFun ((galoisPowerSectionsAddEquiv X F Y n).apply_symm_apply c) σ
  have hg : (fun i => g 0 * v i) = g := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact mul_one (g 0)
    · change g 0 * ((g 0)⁻¹ * g j.succ) = g j.succ
      exact mul_inv_cancel_left _ _
  have hact :
      homogeneousDeckSection X F Y n z (fun i => g 0 * v i) =
        (finiteEtaleDeckSectionsRep X F Y).ρ (g 0)
          (homogeneousDeckSection X F Y n z v) :=
    homogeneousDeckSection_equivariant X F Y n z (g 0) v
  have hvalue := congrArg
    (fun a : F.obj.obj (op ((finiteEtaleInclusion X).obj Y)) =>
      (finiteEtaleDeckSectionsRep X F Y).ρ (g 0) a) hv
  exact (congrArg (homogeneousDeckSection X F Y n z) hg).symm.trans
    (hact.trans (hvalue.trans ((hf (g 0) v).symm.trans (congrArg f hg))))

/-- An actual geometric Cech section defines a morphism from the
standard resolution, by linear extension of homogeneous deck evaluation. -/
def geometricSectionToStandardDeckHom (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) :
    (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).X n ⟶ finiteEtaleDeckSectionsRep X F Y :=
  Rep.ofHom
    { toLinearMap := (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n z)) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap
      isIntertwining' σ := by
        apply MonoidAlgebra.lhom_ext'
        intro g
        change Fin (n + 1) → (Aut Y)ᵐᵒᵖ at g
        apply LinearMap.ext_ring
        change (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n z))
            ((Representation.linearize ℤ (Aut Y)ᵐᵒᵖ
              ((classifyingSpaceUniversalCover (Aut Y)ᵐᵒᵖ).obj (op ⦋n⦌))
              σ (MonoidAlgebra.single g (1 : ℤ))).coeff) =
          (finiteEtaleDeckSectionsRep X F Y).ρ σ
            ((Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n z))
              (Finsupp.single g (1 : ℤ)))
        erw [Representation.linearize_single, MonoidAlgebra.coeff_single]
        change (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n z))
            (Finsupp.single (fun i => σ * g i) (1 : ℤ)) =
          (finiteEtaleDeckSectionsRep X F Y).ρ σ
            ((Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n z))
              (Finsupp.single g (1 : ℤ)))
        erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
          one_smul, one_smul]
        exact homogeneousDeckSection_equivariant X F Y n z σ g }

/-- The standard-resolution morphism evaluates a basis tuple by
actual geometric restriction. -/
theorem geometricSectionToStandardDeckHom_single
    (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) :
    (geometricSectionToStandardDeckHom X F Y n z).hom (MonoidAlgebra.single g (1 : ℤ)) =
      homogeneousDeckSection X F Y n z g := by
  change (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n z))
    (Finsupp.single g (1 : ℤ)) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- Basis evaluation of a standard-resolution morphism has exactly the
actual homogeneous deck equivariance. -/
theorem standardDeckHom_equivariant
    (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) (n : ℕ)
    (a : (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).X n ⟶ finiteEtaleDeckSectionsRep X F Y)
    (σ : (Aut Y)ᵐᵒᵖ) (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) :
    a.hom (MonoidAlgebra.single (fun i => σ * g i) (1 : ℤ)) =
      (finiteEtaleDeckSectionsRep X F Y).ρ σ (a.hom (MonoidAlgebra.single g (1 : ℤ))) := by
  have h := Rep.hom_comm_apply a σ (MonoidAlgebra.single g (1 : ℤ))
  change a.hom (Representation.linearize ℤ (Aut Y)ᵐᵒᵖ
    ((classifyingSpaceUniversalCover (Aut Y)ᵐᵒᵖ).obj (op ⦋n⦌))
      σ (MonoidAlgebra.single g (1 : ℤ))) = _ at h
  erw [Representation.linearize_single] at h
  exact h

/-- The actual geometric construction gives every standard-resolution
cochain, uniquely. -/
theorem geometricSectionToStandardDeckHom_bijective
    (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    Function.Bijective (geometricSectionToStandardDeckHom X F Y n) := by
  constructor
  · intro s t h
    apply homogeneousDeckSection_injective X F Y n
    funext g
    exact (geometricSectionToStandardDeckHom_single X F Y n s g).symm.trans
      ((congrArg (fun a => a.hom (MonoidAlgebra.single g (1 : ℤ))) h).trans
        (geometricSectionToStandardDeckHom_single X F Y n t g))
  · intro a
    obtain ⟨z, hz⟩ := exists_homogeneousDeckSection X F Y n
      (fun g => a.hom (MonoidAlgebra.single g (1 : ℤ)))
      (standardDeckHom_equivariant X F Y n a)
    refine ⟨z, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro g
    change Fin (n + 1) → (Aut Y)ᵐᵒᵖ at g
    apply LinearMap.ext_ring
    exact (geometricSectionToStandardDeckHom_single X F Y n z g).trans (congrFun hz g)

/-- Actual geometric Cech sections and standard-resolution cochains
are additively equivalent in every degree. -/
def geometricSectionStandardDeckHomAddEquiv
    (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))) ≃+
        ((Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).X n ⟶ finiteEtaleDeckSectionsRep X F Y) where
  toEquiv := Equiv.ofBijective (geometricSectionToStandardDeckHom X F Y n)
    (geometricSectionToStandardDeckHom_bijective X F Y n)
  map_add' s t := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro g
    change Fin (n + 1) → (Aut Y)ᵐᵒᵖ at g
    apply LinearMap.ext_ring
    change (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n (s + t)))
        (Finsupp.single g (1 : ℤ)) =
      (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n s))
        (Finsupp.single g (1 : ℤ)) +
      (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n t))
        (Finsupp.single g (1 : ℤ))
    erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, one_smul, one_smul, one_smul]
    exact (F.obj.map ((finiteEtaleInclusion X).map
      (Pi.lift fun i => (MulOpposite.unop (g i)).asIso.hom)).op).hom.map_add s t

/-- Homogeneous evaluation commutes with every actual geometric face. -/
theorem homogeneousDeckSection_face (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ) (i : Fin (n + 2))
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (g : Fin (n + 2) → (Aut Y)ᵐᵒᵖ) :
    homogeneousDeckSection X F Y (n + 1)
      (F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z) g =
        homogeneousDeckSection X F Y n z (fun j => g (i.succAbove j)) := by
  have hg :
      (Pi.lift fun j => (MulOpposite.unop (g j)).asIso.hom) ≫ geometricCechFace Y n i =
        Pi.lift (fun j => (MulOpposite.unop (g (i.succAbove j))).asIso.hom) := by
    apply Pi.hom_ext
    intro j
    dsimp only [geometricCechFace]
    erw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π]
  change F.obj.map ((finiteEtaleInclusion X).map
      (Pi.lift fun j => (MulOpposite.unop (g j)).asIso.hom)).op
      (F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z) =
    F.obj.map ((finiteEtaleInclusion X).map
      (Pi.lift fun j => (MulOpposite.unop (g (i.succAbove j))).asIso.hom)).op z
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    ← Functor.map_comp, hg]

/-- Evaluation on a basis tuple with an arbitrary integer coefficient. -/
theorem geometricSectionToStandardDeckHom_single_coeff
    (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (g : Fin (n + 1) → (Aut Y)ᵐᵒᵖ) (c : ℤ) :
    (geometricSectionToStandardDeckHom X F Y n z).hom (MonoidAlgebra.single g c) =
      c • homogeneousDeckSection X F Y n z g := by
  change (Finsupp.linearCombination ℤ (homogeneousDeckSection X F Y n z))
    (Finsupp.single g c) = _
  exact Finsupp.linearCombination_single ℤ c g

/-- The geometric-to-standard comparison intertwines the actual
alternating Cech differential with the standard group-resolution differential. -/
theorem geometricSectionToStandardDeckHom_d
    (X : Scheme.{0}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{0})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) :
    geometricSectionToStandardDeckHom X F Y (n + 1)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z) =
      (Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).d (n + 1) n ≫
        geometricSectionToStandardDeckHom X F Y n z := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  change (geometricSectionToStandardDeckHom X F Y (n + 1) _).hom
      (MonoidAlgebra.single g (1 : ℤ)) =
    (geometricSectionToStandardDeckHom X F Y n z).hom
      (((Rep.standardComplex ℤ (Aut Y)ᵐᵒᵖ).d (n + 1) n).hom (MonoidAlgebra.single g (1 : ℤ)))
  erw [geometricSectionToStandardDeckHom_single,
    Rep.standardComplex.d_apply, Rep.standardComplex.d_of, map_sum]
  change F.obj.map ((finiteEtaleInclusion X).map
      (Pi.lift fun j => (MulOpposite.unop (g j)).asIso.hom)).op
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z) =
    ∑ i : Fin (n + 2), (geometricSectionToStandardDeckHom X F Y n z).hom
      (MonoidAlgebra.single (g ∘ i.succAbove) ((-1 : ℤ) ^ (i : ℕ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, geometricSectionToStandardDeckHom_single_coeff]
  exact congrArg (fun a => ((-1 : ℤ) ^ (i : ℕ)) • a)
    (homogeneousDeckSection_face X F Y n i z g)

end EtaleCohomology
