/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.RepresentableCechTerms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Geometric Cech faces under finite-product-preserving functors

Canonical product comparison identifies the actual face maps. This is
used for the inclusion of finite etale covers into the small etale site.
-/

@[expose] public section

noncomputable section
universe u v u' v'
open CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]

/-- Canonical product comparison intertwines actual Cech faces. -/
theorem geometricCechFace_map (H : C ⥤ D) [PreservesFiniteProducts H]
    (Y : C) (n : ℕ) (i : Fin (n + 2)) :
    H.map (geometricCechFace Y n i) ≫
        (PreservesProduct.iso H (fun _ : Fin (n + 1) => Y)).hom =
      (PreservesProduct.iso H (fun _ : Fin (n + 2) => Y)).hom ≫
        geometricCechFace (H.obj Y) n i := by
  apply Pi.hom_ext
  intro j
  have hp (m : ℕ) (k : Fin (m + 1)) :
      (PreservesProduct.iso H (fun _ : Fin (m + 1) => Y)).hom ≫
        Pi.π (fun _ : Fin (m + 1) => H.obj Y) k =
      H.map (Pi.π (fun _ : Fin (m + 1) => Y) k) := by
    rw [PreservesProduct.iso_hom, piComparison_comp_π]
  calc
    (H.map (geometricCechFace Y n i) ≫
        (PreservesProduct.iso H (fun _ : Fin (n + 1) => Y)).hom) ≫ Pi.π _ j =
      H.map (geometricCechFace Y n i) ≫ H.map (Pi.π _ j) := by
        erw [Category.assoc, hp n j]
    _ = H.map (Pi.π (fun _ : Fin (n + 2) => Y) (i.succAbove j)) := by
      rw [← H.map_comp]
      exact congrArg H.map (Pi.lift_comp_π _ j)
    _ = ((PreservesProduct.iso H (fun _ : Fin (n + 2) => Y)).hom ≫
        geometricCechFace (H.obj Y) n i) ≫ Pi.π _ j := by
      dsimp only [geometricCechFace]
      erw [Category.assoc, Pi.lift_comp_π, hp (n + 1) (i.succAbove j)]

/-- Actual sheaf sections in the two canonical product presentations. -/
def mappedCechSectionsEquiv (H : C ⥤ D) [PreservesFiniteProducts H]
    (J : GrothendieckTopology D) (Y : C)
    (F : Sheaf J AddCommGrpCat.{v'}) (n : ℕ) :
    F.obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => H.obj Y)) ≃+
      F.obj.obj (op (H.obj (∏ᶜ fun _ : Fin (n + 1) => Y))) :=
  (F.obj.mapIso (PreservesProduct.iso H (fun _ : Fin (n + 1) => Y)).op).addCommGroupIsoToAddEquiv

/-- Product comparison respects actual restriction along each face. -/
theorem mappedCechSectionsEquiv_face (H : C ⥤ D) [PreservesFiniteProducts H]
    (J : GrothendieckTopology D) (Y : C)
    (F : Sheaf J AddCommGrpCat.{v'}) (n : ℕ) (i : Fin (n + 2))
    (z : F.obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => H.obj Y))) :
    mappedCechSectionsEquiv H J Y F (n + 1)
        (F.obj.map (geometricCechFace (H.obj Y) n i).op z) =
      F.obj.map (H.map (geometricCechFace Y n i)).op
        (mappedCechSectionsEquiv H J Y F n z) := by
  change F.obj.map (PreservesProduct.iso H (fun _ : Fin (n + 2) => Y)).hom.op
      (F.obj.map (geometricCechFace (H.obj Y) n i).op z) =
    F.obj.map (H.map (geometricCechFace Y n i)).op
      (F.obj.map (PreservesProduct.iso H (fun _ : Fin (n + 1) => Y)).hom.op z)
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    ← geometricCechFace_map, op_comp, F.obj.map_comp]
  rfl

/-- Product comparison intertwines the full alternating differential. -/
theorem mappedCechSectionsEquiv_d (H : C ⥤ D) [PreservesFiniteProducts H]
    (J : GrothendieckTopology D) (Y : C)
    (F : Sheaf J AddCommGrpCat.{v'}) (n : ℕ)
    (z : F.obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => H.obj Y))) :
    mappedCechSectionsEquiv H J Y F (n + 1)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          F.obj.map (geometricCechFace (H.obj Y) n i).op z) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        F.obj.map (H.map (geometricCechFace Y n i)).op
          (mappedCechSectionsEquiv H J Y F n z) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, mappedCechSectionsEquiv_face]

/-- Injective sheaf coefficients have actual Cech primitives even
when the geometric powers are presented through a product-preserving
inclusion, such as finite etale objects in the small etale site. -/
theorem exists_injective_mappedGeometricCech_primitive
    (H : C ⥤ D) [PreservesFiniteProducts H] (J : GrothendieckTopology D)
    [HasSheafify J AddCommGrpCat.{v'}] (Y : C)
    (I : Sheaf J AddCommGrpCat.{v'}) [Injective I] (n : ℕ)
    (z : I.obj.obj (op (H.obj (∏ᶜ fun _ : Fin (n + 2) => Y))))
    (hz : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      I.obj.map (H.map (geometricCechFace Y (n + 1) i)).op z = 0) :
    ∃ b : I.obj.obj (op (H.obj (∏ᶜ fun _ : Fin (n + 1) => Y))),
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        I.obj.map (H.map (geometricCechFace Y n i)).op b = z := by
  let E := mappedCechSectionsEquiv H J Y I
  let z' := (E (n + 1)).symm z
  have hz' : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      I.obj.map (geometricCechFace (H.obj Y) (n + 1) i).op z' = 0 := by
    apply (E (n + 2)).injective
    erw [mappedCechSectionsEquiv_d, map_zero, AddEquiv.apply_symm_apply]
    exact hz
  obtain ⟨b, hb⟩ := exists_injective_geometricCech_primitive J (H.obj Y) I n z' hz'
  refine ⟨E n b, ?_⟩
  have he := congrArg (E (n + 1)) hb
  erw [mappedCechSectionsEquiv_d, AddEquiv.apply_symm_apply] at he
  exact he

end EtaleCohomology
