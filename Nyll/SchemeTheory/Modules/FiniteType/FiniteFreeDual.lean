/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeLocus
public import Nyll.SchemeTheory.Modules.Sections.IhomSections
public import Mathlib.LinearAlgebra.Dual.Basis
public import Nyll.SchemeTheory.Modules.PresheafInternalHom

/-!
# Evaluation and actual dual sections on a finite trivializing open

A compatible finite basis on all subopens extends each linear functional
on the original sections to a natural family of local functionals. The
existing internal-Hom construction turns this family into an actual dual
section. Thus evaluation identifies dual-sheaf sections with the module
dual on every finite trivializing open, without assuming a sheaf dual
comparison or quasicoherence of the dual.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation of an actual dual-sheaf section as an original linear
functional on sections over the same open. -/
def dualSectionsEvaluation {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(dual M, U) →ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(M, U) where
  toFun t :=
    { toFun := fun m => ihomEval M (𝟙_ X.Modules) U m t
      map_add' := fun m n => ihomEval_add_left U m n t
      map_smul' := fun r m => ihomEval_smul_left U r m t }
  map_add' t s := LinearMap.ext (fun m => ihomEval_add_right U m t s)
  map_smul' r t := LinearMap.ext (fun m => ihomEval_smul_right U r m t)

namespace FiniteFreeDual

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} {n : ℕ}
  (e : Fin n → Γ(M, U))
  (b : ∀ (W : X.Opens), W ≤ U → Module.Basis (Fin n) Γ(X, W) Γ(M, W))
  (hb : ∀ (W : X.Opens) (hWU : W ≤ U) (i : Fin n),
    b W hWU i = M.presheaf.map (homOfLE hWU).op (e i))

include hb in
private theorem basis_map {W Z : X.Opens} (hWU : W ≤ U) (g : Z ⟶ W) (i : Fin n) :
    M.presheaf.map g.op (b W hWU i) = b Z (g.le.trans hWU) i := by
  rw [hb, hb]
  exact (congrArg (fun k : Γ(M, U) ⟶ Γ(M, Z) => k (e i))
    (M.presheaf.map_comp (homOfLE hWU).op g.op)).symm

private def localFunctional (l : Module.Dual Γ(X, U) Γ(M, U))
    (W : X.Opens) (hWU : W ≤ U) : Module.Dual Γ(X, W) Γ(M, W) :=
  (b W hWU).constr Γ(X, W)
    (fun i => X.presheaf.map (homOfLE hWU).op (l (e i)))

private theorem localFunctional_basis (l : Module.Dual Γ(X, U) Γ(M, U))
    (W : X.Opens) (hWU : W ≤ U) (i : Fin n) :
    localFunctional M e b l W hWU (b W hWU i) =
      X.presheaf.map (homOfLE hWU).op (l (e i)) :=
  (b W hWU).constr_basis Γ(X, W) _ i

include hb in
private theorem localFunctional_naturality (l : Module.Dual Γ(X, U) Γ(M, U))
    {W Z : X.Opens} (hWU : W ≤ U) (g : Z ⟶ W) (m : Γ(M, W)) :
    X.presheaf.map g.op (localFunctional M e b l W hWU m) =
      localFunctional M e b l Z (g.le.trans hWU) (M.presheaf.map g.op m) := by
  let σ : Γ(X, W) →+* Γ(X, Z) := (X.presheaf.map g.op).hom
  let a : Γ(M, W) →ₛₗ[σ] Γ(X, Z) :=
    { toFun := fun x => X.presheaf.map g.op (localFunctional M e b l W hWU x)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun r x => by
        rw [(localFunctional M e b l W hWU).map_smul]
        exact (X.presheaf.map g.op).hom.map_mul r _ }
  let c : Γ(M, W) →ₛₗ[σ] Γ(X, Z) :=
    { toFun := fun x => localFunctional M e b l Z (g.le.trans hWU)
          (M.presheaf.map g.op x)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun r x => by
        rw [M.map_smul g r x]
        exact (localFunctional M e b l Z (g.le.trans hWU)).map_smul _ _ }
  have hac : a = c := by
    apply (b W hWU).ext
    intro i
    change X.presheaf.map g.op (localFunctional M e b l W hWU (b W hWU i)) =
      localFunctional M e b l Z (g.le.trans hWU) (M.presheaf.map g.op (b W hWU i))
    rw [localFunctional_basis, basis_map M e b hb, localFunctional_basis]
    exact (congrArg (fun k : Γ(X, U) ⟶ Γ(X, Z) => k (l (e i)))
      (X.presheaf.map_comp (homOfLE hWU).op g.op)).symm
  exact LinearMap.congr_fun hac m

private def functionalFamily (l : Module.Dual Γ(X, U) Γ(M, U)) :
    PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M)
      ((toPMod X).obj (𝟙_ X.Modules)) (op U) :=
  ⟨fun W f => localFunctional M e b l W.unop f.unop.le, by
    intro W Z f g m
    exact localFunctional_naturality M e b hb l f.unop.le g.unop m⟩

private def sectionOfFunctional (l : Module.Dual Γ(X, U) Γ(M, U)) : Γ(dual M, U) :=
  (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property
    M (𝟙_ X.Modules) (op U)).symm (functionalFamily M e b hb l)

private theorem sectionOfFunctional_eval (l : Module.Dual Γ(X, U) Γ(M, U))
    (W : X.Opens) (hWU : W ≤ U) (m : Γ(M, W)) :
    ihomEval M (𝟙_ X.Modules) W m
        ((dual M).presheaf.map (homOfLE hWU).op (sectionOfFunctional M e b hb l)) =
      localFunctional M e b l W hWU m := by
  have h := SheafOfModules.ihomSectionsEquivFamily_app_eq_ihomEval
    X.sheaf.obj X.ringCatSheaf.property
    (M := M) (N := 𝟙_ X.Modules) (homOfLE hWU).op
    (sectionOfFunctional M e b hb l) m
  rw [sectionOfFunctional, AddEquiv.apply_symm_apply] at h
  exact h.symm

include hb in
private theorem localFunctional_top (l : Module.Dual Γ(X, U) Γ(M, U)) :
    localFunctional M e b l U le_rfl = l := by
  apply (b U le_rfl).ext
  intro i
  rw [localFunctional_basis, hb]
  have h : (homOfLE (show U ≤ U from le_rfl)).op = 𝟙 (op U) := Subsingleton.elim _ _
  rw [h, X.presheaf.map_id, M.presheaf.map_id]
  rfl

end FiniteFreeDual

/-- On a finite trivializing open, evaluation of actual dual sections
is bijective. Surjectivity constructs the natural functional family on
every smaller open from the original compatible basis. -/
theorem dualSectionsEvaluation_bijective_of_isFiniteFreeOn
    {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsFiniteFreeOn M U) :
    Function.Bijective (dualSectionsEvaluation M U) := by
  classical
  obtain ⟨n, e, he⟩ := hU
  choose b hb using he
  constructor
  · intro t s hts
    apply ihom_sections_ext
    intro W i m
    let lt := dualSectionsEvaluation M W ((dual M).presheaf.map i.op t)
    let ls := dualSectionsEvaluation M W ((dual M).presheaf.map i.op s)
    have hlocal : lt = ls := by
      apply (b W i.le).ext
      intro a
      change ihomEval M (𝟙_ X.Modules) W (b W i.le a)
          ((dual M).presheaf.map i.op t) =
        ihomEval M (𝟙_ X.Modules) W (b W i.le a)
          ((dual M).presheaf.map i.op s)
      rw [hb]
      exact (map_ihomEval (M := M) (N := 𝟙_ X.Modules) i (e a) t).symm.trans
        ((congrArg (fun r : Γ(X, U) => X.presheaf.map i.op r)
          (LinearMap.congr_fun hts (e a))).trans
          (map_ihomEval (M := M) (N := 𝟙_ X.Modules) i (e a) s))
    exact LinearMap.congr_fun hlocal m
  · intro l
    refine ⟨FiniteFreeDual.sectionOfFunctional M e b hb l, ?_⟩
    ext m
    have h := FiniteFreeDual.sectionOfFunctional_eval M e b hb l U le_rfl m
    have hid : (homOfLE (show U ≤ U from le_rfl)).op = 𝟙 (op U) :=
      Subsingleton.elim _ _
    rw [hid, (dual M).presheaf.map_id] at h
    exact h.trans (LinearMap.congr_fun (FiniteFreeDual.localFunctional_top M e b hb l) m)

/-- The original section module of the dual is identified with the
linear dual by the actual evaluation map on a finite trivializing open. -/
def dualSectionsEquivOfIsFiniteFreeOn
    {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsFiniteFreeOn M U) :
    Γ(dual M, U) ≃ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(M, U) :=
  LinearEquiv.ofBijective (dualSectionsEvaluation M U)
    (dualSectionsEvaluation_bijective_of_isFiniteFreeOn M hU)

/-- The dual basis consists of actual dual sections, and its restrictions
are the dual bases on all smaller opens. Thus finite local freeness is
preserved by the actual internal dual sheaf. -/
theorem IsFiniteFreeOn.dual {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (hU : IsFiniteFreeOn M U) : IsFiniteFreeOn (Scheme.Modules.dual M) U := by
  classical
  obtain ⟨n, e, he⟩ := hU
  choose b hb using he
  have hfree : IsFiniteFreeOn M U := ⟨n, e, fun W h => ⟨b W h, hb W h⟩⟩
  let E := dualSectionsEquivOfIsFiniteFreeOn M hfree
  let d : Fin n → Γ(Scheme.Modules.dual M, U) :=
    fun i => E.symm ((b U le_rfl).dualBasis i)
  refine ⟨n, d, ?_⟩
  intro W hWU
  let EW := dualSectionsEquivOfIsFiniteFreeOn M (IsFiniteFreeOn.mono M hfree hWU)
  refine ⟨(b W hWU).dualBasis.map EW.symm, ?_⟩
  intro i
  apply EW.injective
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  apply (b W hWU).ext
  intro j
  have heU (a : Fin n) : b U le_rfl a = e a := by
    rw [hb]
    have hid : (homOfLE (show U ≤ U from le_rfl)).op = 𝟙 (op U) :=
      Subsingleton.elim _ _
    rw [hid, M.presheaf.map_id]
    rfl
  have hd (a : Fin n) :
      ihomEval M (𝟙_ X.Modules) U (e a) (d i) =
        (b U le_rfl).dualBasis i (b U le_rfl a) := by
    have h := LinearMap.congr_fun (E.apply_symm_apply ((b U le_rfl).dualBasis i)) (e a)
    exact h.trans (congrArg ((b U le_rfl).dualBasis i) (heU a).symm)
  change (b W hWU).dualBasis i (b W hWU j) =
    ihomEval M (𝟙_ X.Modules) W (b W hWU j)
      ((Scheme.Modules.dual M).presheaf.map (homOfLE hWU).op (d i))
  have hres := map_ihomEval (M := M) (N := 𝟙_ X.Modules)
    (homOfLE hWU) (e j) (d i)
  rw [← hb W hWU j, hd, Module.Basis.dualBasis_apply_self] at hres
  rw [Module.Basis.dualBasis_apply_self]
  change X.presheaf.map (homOfLE hWU).op (if j = i then 1 else 0) = _ at hres
  by_cases hij : j = i
  · subst j
    simpa only [ite_true, map_one] using hres
  · simpa only [hij, ite_false, map_zero] using hres

/-- The actual finite locally free locus of a module is contained in
the finite locally free locus of its internal dual. -/
theorem finiteFreeLocus_le_dual {X : Scheme.{u}} (M : X.Modules) :
    finiteFreeLocus M ≤ finiteFreeLocus (dual M) := by
  intro x hx
  obtain ⟨U, hxU, hU⟩ := (mem_finiteFreeLocus_iff M x).mp hx
  exact (mem_finiteFreeLocus_iff (dual M) x).mpr ⟨U, hxU, hU.dual⟩

end AlgebraicGeometry.Scheme.Modules
