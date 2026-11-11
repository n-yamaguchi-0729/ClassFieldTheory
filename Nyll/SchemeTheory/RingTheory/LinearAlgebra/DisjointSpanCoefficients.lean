/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Choose

/-!
# Coefficients in a disjoint span after extending scalars

The finite-family form of linear disjointness forces a linear combination to have zero
coefficients when it lies in the extended span of a disjoint base-field submodule. This is the
shared linear-algebra argument used by both place-restriction degree computations. The field
embeddings, coefficients and submodule are the supplied ones.
-/

@[expose] public section

noncomputable section

namespace LinearIndependent

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

/-- Under the finite-family linear-disjointness condition, a combination of an independent
family cannot belong to the extended span of a disjoint submodule unless its coefficients vanish.
All maps are the original algebra maps into the given common field. -/
theorem coeff_eq_zero_of_disjoint_span_image
    {m : ℕ} {f₀ : Fin m → F₀} (hlin : LinearIndependent k f₀)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    {N : Submodule k F₀} (hdis : Disjoint (Submodule.span k (Set.range f₀)) N)
    (a : Fin m → K) {y : F}
    (hy : y ∈ Submodule.span K (algebraMap F₀ F '' (N : Set F₀)))
    (h : ∑ i, a i • algebraMap F₀ F (f₀ i) = y) : ∀ i, a i = 0 := by
  classical
  rw [Submodule.mem_span_set'] at hy
  obtain ⟨n, c, g, rfl⟩ := hy
  have hg : ∀ j, ∃ f : F₀, f ∈ (N : Set F₀) ∧ algebraMap F₀ F f = (g j : F) :=
    fun j => (g j).2
  choose f hfN hfι using hg
  obtain ⟨b, hbt, hspan, hbind⟩ := exists_linearIndependent k (Set.range f)
  have hbfin : b.Finite := (Set.finite_range f).subset hbt
  let : Fintype b := hbfin.fintype
  have hrange : Set.range (fun z : b => algebraMap F₀ F (z : F₀)) =
      algebraMap F₀ F '' b := by
    ext y
    simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]
  have hy' : (∑ j, c j • (g j : F)) ∈
      Submodule.span K (Set.range fun z : b => algebraMap F₀ F (z : F₀)) := by
    rw [hrange]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    rw [← hfι j]
    have hfspan : f j ∈ Submodule.span k b := by
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact ((Submodule.image_span_subset
      (IsScalarTower.toAlgHom k F₀ F).toLinearMap b
      ((Submodule.span K (algebraMap F₀ F '' b)).restrictScalars k)).2
      (fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩)) ⟨f j, hfspan, rfl⟩
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
  let w : Fin m ⊕ b → F₀ := Sum.elim f₀ (fun z => (z : F₀))
  have hw : LinearIndependent k w := by
    apply LinearIndependent.sum_type hlin hbind
    refine hdis.mono_right ?_
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hfN j
  let coef : Fin m ⊕ b → K := Sum.elim a (fun z => - c' z)
  have hrel : ∑ x, algebraMap K F (coef x) * algebraMap F₀ F (w x) = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [w, coef, Sum.elim_inl, Sum.elim_inr, map_neg, neg_mul,
      Finset.sum_neg_distrib]
    have e1 : ∑ i : Fin m, algebraMap K F (a i) * algebraMap F₀ F (f₀ i) =
        ∑ i, a i • algebraMap F₀ F (f₀ i) := by
      simp only [Algebra.smul_def]
    have e2 : ∑ z : b, algebraMap K F (c' z) * algebraMap F₀ F (z : F₀) =
        ∑ z : b, c' z • algebraMap F₀ F (z : F₀) := by
      simp only [Algebra.smul_def]
    rw [e1, e2, h, hc', add_neg_cancel]
  let e := (Fintype.equivFin (Fin m ⊕ b)).symm
  have hsum : ∑ i, algebraMap K F ((coef ∘ e) i) * algebraMap F₀ F ((w ∘ e) i) = 0 := by
    rw [show ∑ i, algebraMap K F ((coef ∘ e) i) * algebraMap F₀ F ((w ∘ e) i)
        = ∑ x, algebraMap K F (coef x) * algebraMap F₀ F (w x) from
      Equiv.sum_comp e (fun x => algebraMap K F (coef x) * algebraMap F₀ F (w x))]
    exact hrel
  have hLD' := hLD _ (w ∘ e) (coef ∘ e) (hw.comp e e.injective) hsum
  intro i
  have hzero := hLD' (e.symm (Sum.inl i))
  change coef (e (e.symm (Sum.inl i))) = 0 at hzero
  rw [e.apply_symm_apply] at hzero
  exact hzero

end LinearIndependent
