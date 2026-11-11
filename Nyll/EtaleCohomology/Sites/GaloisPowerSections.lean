/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.FiniteCoproductSections
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FinitePowers

/-!
# All-degree actual deck coordinates of sheaf sections

Sections on every finite positive power of a finite etale Galois cover
are functions of tuples of actual deck transformations. The equivalence
is obtained from the geometric deck decomposition and actual sheaf descent.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleCohomology

/-- Actual sections on a finite power are deck-tuple coordinates. -/
def galoisPowerSectionsEquiv
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))) ≃
        ((Fin n → Aut Y) → F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) :=
  (F.obj.mapIso ((finiteEtaleInclusion X).mapIso
    (galoisPowerIso Y n)).op).toEquiv.trans
      (finiteEtaleSheafCoproductSectionsEquiv X F (fun _ : Fin n → Aut Y => Y))

/-- A deck-tuple coordinate is restriction along the actual deck graph. -/
theorem galoisPowerSectionsEquiv_apply
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (s : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) (σ : Fin n → Aut Y) :
    galoisPowerSectionsEquiv X F Y n s σ =
      F.obj.map ((finiteEtaleInclusion X).map (galoisPowerGraph Y n σ)).op s := by
  rw [galoisPowerSectionsEquiv, Equiv.trans_apply,
    finiteEtaleSheafCoproductSectionsEquiv_apply]
  change F.obj.map ((finiteEtaleInclusion X).map
      (Sigma.ι (fun _ : Fin n → Aut Y => Y) σ)).op
    (F.obj.map ((finiteEtaleInclusion X).map (galoisPowerIso Y n).hom).op s) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    ← Functor.map_comp, galoisPowerIso_ι]

/-- The actual deck-coordinate equivalence is additive for abelian
coefficient sheaves in every degree. -/
def galoisPowerSectionsAddEquiv
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y))) ≃+
        ((Fin n → Aut Y) → F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) where
  toEquiv := galoisPowerSectionsEquiv X
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F) Y n
  map_add' s t := by
    funext σ
    let U := (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F
    have he (a : F.obj.obj (op ((finiteEtaleInclusion X).obj
        (∏ᶜ fun _ : Fin (n + 1) => Y)))) :
        (galoisPowerSectionsEquiv X U Y n a σ :
          F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) =
        F.obj.map ((finiteEtaleInclusion X).map (galoisPowerGraph Y n σ)).op a :=
      galoisPowerSectionsEquiv_apply X U Y n a σ
    exact (he (s + t)).trans
      (((F.obj.map ((finiteEtaleInclusion X).map
        (galoisPowerGraph Y n σ)).op).hom.map_add s t).trans
        (congrArg₂ (fun a b : F.obj.obj (op ((finiteEtaleInclusion X).obj Y)) => a + b)
          (he s).symm (he t).symm))

/-- Additive deck coordinates evaluate on their geometric graph. -/
theorem galoisPowerSectionsAddEquiv_apply
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (s : F.obj.obj (op ((finiteEtaleInclusion X).obj
      (∏ᶜ fun _ : Fin (n + 1) => Y)))) (σ : Fin n → Aut Y) :
    galoisPowerSectionsAddEquiv X F Y n s σ =
      F.obj.map ((finiteEtaleInclusion X).map (galoisPowerGraph Y n σ)).op s :=
  galoisPowerSectionsEquiv_apply X
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F) Y n s σ

/-- Deck coordinates for the actual product in the small etale site,
using the proved preservation of finite products by the inclusion. -/
def galoisEtalePowerSectionsAddEquiv
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ) :
    F.obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => (finiteEtaleInclusion X).obj Y)) ≃+
      ((Fin n → Aut Y) → F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) :=
  ((F.obj.mapIso (PreservesProduct.iso (finiteEtaleInclusion X)
      (fun _ : Fin (n + 1) => Y)).op).addCommGroupIsoToAddEquiv).trans
    (galoisPowerSectionsAddEquiv X F Y n)

/-- Each coordinate of the actual small-etale product equivalence is
restriction along its actual mapped deck graph. -/
theorem galoisEtalePowerSectionsAddEquiv_apply
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] (n : ℕ)
    (s : F.obj.obj (op
      (∏ᶜ fun _ : Fin (n + 1) => (finiteEtaleInclusion X).obj Y)))
    (σ : Fin n → Aut Y) :
    galoisEtalePowerSectionsAddEquiv X F Y n s σ =
      F.obj.map
        ((finiteEtaleInclusion X).map (galoisPowerGraph Y n σ) ≫
          (PreservesProduct.iso (finiteEtaleInclusion X)
            (fun _ : Fin (n + 1) => Y)).hom).op s := by
  change galoisPowerSectionsAddEquiv X F Y n
    (F.obj.map (PreservesProduct.iso (finiteEtaleInclusion X)
      (fun _ : Fin (n + 1) => Y)).hom.op s) σ = _
  rw [galoisPowerSectionsAddEquiv_apply, op_comp, F.obj.map_comp]
  rfl

end EtaleCohomology
