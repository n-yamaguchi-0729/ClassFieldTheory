/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct

/-!
# All finite powers of an actual Galois cover

A tuple of actual deck transformations describes all coordinates relative
to a distinguished first coordinate. These deck graphs decompose every
finite positive power of a Galois object. The proof uses the actual fiber
functor and its simply transitive deck action.
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]

/-- The graph of a finite tuple of deck transformations, with first
coordinate the identity. -/
def galoisPowerGraph (X : C) (n : ℕ) (σ : Fin n → Aut X) :
    X ⟶ ∏ᶜ fun _ : Fin (n + 1) => X :=
  Pi.lift (Fin.cases (𝟙 X) (fun i => (σ i).asIso.hom))

/-- The union of all actual deck graphs in a finite positive power. -/
def galoisPowerMap (X : C) [IsGalois X] (n : ℕ) :
    (∐ fun _ : Fin n → Aut X => X) ⟶ ∏ᶜ fun _ : Fin (n + 1) => X :=
  Sigma.desc (galoisPowerGraph X n)

/-- Every finite positive power of a Galois object is decomposed by its
actual deck graphs. -/
theorem galoisPowerMap_isIso (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (X : C) [IsGalois X] (n : ℕ) : IsIso (galoisPowerMap X n) := by
  classical
  let T : C ⥤ Type w := F ⋙ FintypeCat.incl
  let A := fun _ : Fin n → Aut X => X
  let B := fun _ : Fin (n + 1) => X
  have hrep : ∀ a : F.obj (∐ A), ∃ (σ : Fin n → Aut X) (x : F.obj X),
      F.map (Sigma.ι A σ) x = a := by
    intro a
    obtain ⟨σ, x, hx⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfHasCoproductOfPreservesColimit T A) a
    exact ⟨σ.as, x, hx⟩
  let a (σ : Fin n → Aut X) (x : F.obj X) :=
    F.map (galoisPowerMap X n) (F.map (Sigma.ι A σ) x)
  have h₀ (σ : Fin n → Aut X) (x : F.obj X) :
      F.map (Pi.π B 0) (a σ x) = x := by
    simp only [a, A, B, galoisPowerMap, galoisPowerGraph,
      ← FintypeCat.comp_apply, ← Functor.map_comp,
      Sigma.ι_comp_desc, Pi.lift_comp_π, Fin.cases_zero,
      Functor.map_id, FintypeCat.id_apply]
  have h₁ (σ : Fin n → Aut X) (x : F.obj X) (i : Fin n) :
      F.map (Pi.π B i.succ) (a σ x) = F.map (σ i).asIso.hom x := by
    simp only [a, A, B, galoisPowerMap, galoisPowerGraph,
      ← FintypeCat.comp_apply, ← Functor.map_comp,
      Sigma.ι_comp_desc, Pi.lift_comp_π, Fin.cases_succ]
  have hbij : Function.Bijective (F.map (galoisPowerMap X n)) := by
    constructor
    · intro b c h
      obtain ⟨σ, x, rfl⟩ := hrep b
      obtain ⟨τ, y, rfl⟩ := hrep c
      change a σ x = a τ y at h
      have hxy : x = y := by
        exact (h₀ σ x).symm.trans
          ((congrArg (F.map (Pi.π B 0)) h).trans (h₀ τ y))
      subst y
      have hστ : σ = τ := by
        funext i
        apply evaluation_aut_injective_of_isConnected F X x
        exact (h₁ σ x i).symm.trans
          ((congrArg (F.map (Pi.π B i.succ)) h).trans (h₁ τ x i))
      subst τ
      rfl
    · intro z
      let x := F.map (Pi.π B 0) z
      have hex (i : Fin n) : ∃ σ : Aut X,
          F.map σ.asIso.hom x = F.map (Pi.π B i.succ) z :=
        evaluation_aut_surjective_of_isGalois F X x _
      let σ : Fin n → Aut X := fun i => Classical.choose (hex i)
      refine ⟨F.map (Sigma.ι A σ) x, ?_⟩
      apply Concrete.isLimit_ext (Discrete.functor B ⋙ F)
        (isLimitOfPreserves F (limit.isLimit (Discrete.functor B)))
      rintro ⟨j⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · exact h₀ σ x
      · exact (h₁ σ x i).trans (Classical.choose_spec (hex i))
  have : IsIso (F.map (galoisPowerMap X n)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact isIso_of_reflects_iso (galoisPowerMap X n) F

/-- The canonical actual deck decomposition of a finite positive power. -/
def galoisPowerIso (X : C) [IsGalois X] (n : ℕ) :
    (∐ fun _ : Fin n → Aut X => X) ≅ ∏ᶜ fun _ : Fin (n + 1) => X := by
  have : IsIso (galoisPowerMap X n) :=
    galoisPowerMap_isIso (CategoryTheory.GaloisCategory.getFiberFunctor C) X n
  exact asIso (galoisPowerMap X n)

/-- A component of the decomposition is its actual deck graph. -/
theorem galoisPowerIso_ι (X : C) [IsGalois X] (n : ℕ) (σ : Fin n → Aut X) :
    Sigma.ι (fun _ : Fin n → Aut X => X) σ ≫ (galoisPowerIso X n).hom =
      galoisPowerGraph X n σ :=
  Sigma.ι_comp_desc _ σ

end CategoryTheory.PreGaloisCategory
