/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.InjectiveDeckCohomology
public import Nyll.EtaleCohomology.Classical.FieldSectionRepresentations
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# Homogeneous-function primitives from actual etale descent

The already proved geometric Cech primitives give equivariant
homogeneous-function primitives in every positive degree.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

/-- Actual homogeneous evaluation respects the alternating face differential. -/
theorem homogeneousDeckSection_d
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) (n : ℕ)
    (z : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))))
    (a : Fin (n + 2) → (Aut Y)ᵐᵒᵖ) :
    homogeneousDeckSection X F Y (n + 1)
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        F.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y n i)).op z) a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        homogeneousDeckSection X F Y n z (fun j => a (i.succAbove j)) := by
  change F.obj.map ((finiteEtaleInclusion X).map
    (Pi.lift fun j => (MulOpposite.unop (a j)).asIso.hom)).op _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  exact congrArg (fun x => ((-1 : ℤ) ^ (i : ℕ)) • x)
    (homogeneousDeckSection_face X F Y n i z a)

/-- Every positive-degree homogeneous cocycle on an actual Galois cover,
with actual injective sheaf coefficients, has an equivariant primitive. -/
theorem exists_injective_homogeneousDeck_primitive
    (X : Scheme.{u}) [ConnectedSpace X]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (f : (Fin (n + 2) → (Aut Y)ᵐᵒᵖ) →
      I.obj.obj (op ((finiteEtaleInclusion X).obj Y)))
    (heq : ∀ (σ : (Aut Y)ᵐᵒᵖ) (a : Fin (n + 2) → (Aut Y)ᵐᵒᵖ),
      f (fun i => σ * a i) = (finiteEtaleDeckSectionsRep X I Y).ρ σ (f a))
    (hc : ∀ a : Fin (n + 3) → (Aut Y)ᵐᵒᵖ,
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • f (fun j => a (i.succAbove j)) = 0) :
    ∃ g : (Fin (n + 1) → (Aut Y)ᵐᵒᵖ) →
        I.obj.obj (op ((finiteEtaleInclusion X).obj Y)),
      (∀ (σ : (Aut Y)ᵐᵒᵖ) (a : Fin (n + 1) → (Aut Y)ᵐᵒᵖ),
        g (fun i => σ * a i) = (finiteEtaleDeckSectionsRep X I Y).ρ σ (g a)) ∧
      ∀ a : Fin (n + 2) → (Aut Y)ᵐᵒᵖ,
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • g (fun j => a (i.succAbove j)) = f a := by
  obtain ⟨z, hz⟩ := exists_homogeneousDeckSection X I Y (n + 1) f heq
  have hdz : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      I.obj.map ((finiteEtaleInclusion X).map (geometricCechFace Y (n + 1) i)).op z = 0 := by
    apply homogeneousDeckSection_injective X I Y (n + 2)
    funext a
    rw [homogeneousDeckSection_d, hz]
    exact (hc a).trans
      ((I.obj.map ((finiteEtaleInclusion X).map
        (Pi.lift fun j => (MulOpposite.unop (a j)).asIso.hom)).op).hom.map_zero).symm
  obtain ⟨b, hb⟩ := exists_injective_mappedGeometricCech_primitive
    (finiteEtaleInclusion X) X.smallEtaleTopology Y I n z hdz
  refine ⟨homogeneousDeckSection X I Y n b,
    homogeneousDeckSection_equivariant X I Y n b, ?_⟩
  intro a
  exact (homogeneousDeckSection_d X I Y n b a).symm.trans
    ((congrArg (fun z => homogeneousDeckSection X I Y (n + 1) z a) hb).trans
      (congrFun hz a))

/-- Actual finite-field Galois homogeneous cocycles of an injective etale sheaf
have primitives, through the proved field/deck identification. -/
theorem exists_injective_homogeneousFieldGalois_primitive
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (n : ℕ)
    (f : (Fin (n + 2) → Gal(L/K)) →
      I.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj
        (FiniteEtale.mk (ξ K L)))))
    (heq : ∀ (σ : Gal(L/K)) (a : Fin (n + 2) → Gal(L/K)),
      f (fun i => σ * a i) = (fieldGaloisSheafAction K L I σ).asIso.hom (f a))
    (hc : ∀ a : Fin (n + 3) → Gal(L/K),
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • f (fun j => a (i.succAbove j)) = 0) :
    ∃ g : (Fin (n + 1) → Gal(L/K)) →
        I.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj
          (FiniteEtale.mk (ξ K L)))),
      (∀ (σ : Gal(L/K)) (a : Fin (n + 1) → Gal(L/K)),
        g (fun i => σ * a i) = (fieldGaloisSheafAction K L I σ).asIso.hom (g a)) ∧
      ∀ a : Fin (n + 2) → Gal(L/K),
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • g (fun j => a (i.succAbove j)) = f a := by
  let X := Spec (.of K)
  let Y : FiniteEtale X := FiniteEtale.mk (ξ K L)
  let e : Gal(L/K) ≃* (Aut Y)ᵐᵒᵖ :=
    EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L
  let fD (a : Fin (n + 2) → (Aut Y)ᵐᵒᵖ) := f (fun i => e.symm (a i))
  have heqD (σ : (Aut Y)ᵐᵒᵖ) (a : Fin (n + 2) → (Aut Y)ᵐᵒᵖ) :
      fD (fun i => σ * a i) = (finiteEtaleDeckSectionsRep X I Y).ρ σ (fD a) := by
    have ht : (fun i => e.symm (σ * a i)) =
        (fun i => e.symm σ * e.symm (a i)) := funext (fun i => e.symm.map_mul σ (a i))
    have ha : (fieldGaloisSheafAction K L I (e.symm σ)).asIso.hom (fD a) =
        (finiteEtaleDeckSectionsRep X I Y).ρ σ (fD a) := by
      change (finiteEtaleSheafDeckAction X I Y (e (e.symm σ))).asIso.hom (fD a) =
        (finiteEtaleSheafDeckAction X I Y σ).asIso.hom (fD a)
      rw [e.apply_symm_apply]
    exact (congrArg f ht).trans ((heq (e.symm σ) (fun i => e.symm (a i))).trans ha)
  have hcD (a : Fin (n + 3) → (Aut Y)ᵐᵒᵖ) :
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • fD (fun j => a (i.succAbove j)) = 0 :=
    hc (fun i => e.symm (a i))
  have : PreGaloisCategory.IsGalois Y :=
    EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L
  obtain ⟨gD, hgD, hdD⟩ :=
    exists_injective_homogeneousDeck_primitive X I Y n fD heqD hcD
  refine ⟨fun a => gD (fun i => e (a i)), ?_, ?_⟩
  · intro σ a
    have ht : (fun i => e (σ * a i)) =
        (fun i => e σ * e (a i)) := funext (fun i => e.map_mul σ (a i))
    exact (congrArg gD ht).trans (hgD (e σ) (fun i => e (a i)))
  · intro a
    have ht : (fun i => e.symm (e (a i))) = a :=
      funext (fun i => e.symm_apply_apply (a i))
    exact (hdD (fun i => e (a i))).trans (congrArg f ht)

end EtaleCohomology
