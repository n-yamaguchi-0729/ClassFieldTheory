/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The actual finite constant field of an open arithmetic subgroup

The comparison remembers the original action on the algebraic closure, rather
than merely supplying an abstract isomorphism of procyclic groups. This is the
constant-field input for restricting a geometric section to its actual finite
field of definition.
-/

@[expose] public section

noncomputable section

namespace KummerTheory

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsGalois k κ]

/-- Every open constant subgroup is the relative Galois group of its actual
fixed field, with unchanged action on the given closure. -/
theorem exists_finiteIntermediateField_openSubgroup_equiv_apply
    (G : OpenSubgroup Gal(κ/k)) :
    ∃ E : IntermediateField k κ, FiniteDimensional k E ∧
      E.fixingSubgroup = G.toSubgroup ∧
      ∃ e : G ≃ₜ* Gal(κ/E), ∀ (σ : G) (x : κ), e σ x = (σ : Gal(κ/k)) x := by
  let E : IntermediateField k κ := IntermediateField.fixedField G.toSubgroup
  let C : ClosedSubgroup Gal(κ/k) := ⟨G.toSubgroup, G.isClosed⟩
  have hfix : E.fixingSubgroup = G.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField C
  have hfin : FiniteDimensional k E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by rw [hfix]; exact G.isOpen)
  have : FiniteDimensional k E := hfin
  let e₀ : G ≃ₜ* E.fixingSubgroup :=
    { toMulEquiv := MulEquiv.subgroupCongr hfix.symm
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val
        (fun σ => hfix.symm ▸ σ.property)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val
        (fun σ => hfix ▸ σ.property) }
  exact ⟨E, hfin, hfix, e₀.trans (fixingSubgroupContinuousEquiv E), fun _ _ => rfl⟩

/-- Over a finite base, an open subgroup contains the fixing subgroup of a
finite Galois constant field with a nontrivial multiplicative group. The
additional constant is chosen inside the same prescribed closure. -/
theorem exists_finiteGaloisIntermediateField_fixing_le_of_open
    [Finite k] [IsAlgClosed κ] (G : OpenSubgroup Gal(κ/k)) :
    ∃ E : FiniteGaloisIntermediateField k κ,
      E.fixingSubgroup ≤ G.toSubgroup ∧ 1 < Nat.card Eˣ := by
  classical
  obtain ⟨E₀, hfin, hfix, -, -⟩ :=
    exists_finiteIntermediateField_openSubgroup_equiv_apply G
  have : FiniteDimensional k E₀ := hfin
  have : Finite E₀ := Module.finite_of_finite k
  let D : FiniteGaloisIntermediateField k κ := .mk E₀
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset κ)
  have ht0 : t ≠ 0 := fun h => ht (Finset.mem_insert.mpr (Or.inl h))
  have ht1 : t ≠ 1 := fun h =>
    ht (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
  let E := D ⊔ FiniteGaloisIntermediateField.adjoin k ({t} : Set κ)
  have hDE : E₀ ≤ E.toIntermediateField := by
    change D.toIntermediateField ≤ E.toIntermediateField
    exact (FiniteGaloisIntermediateField.le_iff D E).mp le_sup_left
  have htE : t ∈ E.toIntermediateField :=
    ((FiniteGaloisIntermediateField.le_iff
      (FiniteGaloisIntermediateField.adjoin k ({t} : Set κ)) E).mp le_sup_right)
      (FiniteGaloisIntermediateField.subset_adjoin k ({t} : Set κ) (Set.mem_singleton t))
  refine ⟨E, ?_, ?_⟩
  · rw [← hfix]
    intro σ hσ
    apply (IntermediateField.mem_fixingSubgroup_iff E₀ σ).mpr
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField σ).mp hσ x (hDE hx)
  · let tE : E := ⟨t, htE⟩
    have htE0 : tE ≠ 0 := fun h => ht0 (congrArg (fun x : E => (x : κ)) h)
    let u : Eˣ := Units.mk0 tE htE0
    have hu : u ≠ 1 := fun h => ht1 (congrArg (fun a : Eˣ => ((a : E) : κ)) h)
    have : Nontrivial Eˣ := ⟨⟨u, 1, hu⟩⟩
    have : Finite E := Module.finite_of_finite k
    let : Fintype E := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

end KummerTheory
