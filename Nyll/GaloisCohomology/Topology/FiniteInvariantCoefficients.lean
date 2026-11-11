/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Sylow
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite invariant coefficients in discrete continuous representations

For a compact group and a finite scalar ring, each finite subset of a
discrete continuous representation lies in a finite invariant submodule.
The construction reuses finite compact images and the existing finiteness
theorem for spans over finite rings.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory

namespace TopRep

variable (R : Type v) [Ring R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G]
  [CompactSpace G] (X : TopRep.{u} R G) [DiscreteTopology X]

/-- A finite subset of discrete continuous coefficients is contained in a
finitely generated invariant submodule, using the span of its finite orbits. -/
theorem exists_fg_invariant_submodule
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (s : Set X) (hs : s.Finite) :
    ∃ W : Submodule R X, s ⊆ W ∧ W.FG ∧
      ∀ g : G, W ≤ W.comap (X.ρ g).toLinearMap := by
  let t : Set X := ⋃ x ∈ s, Set.range (fun g : G => X.ρ g x)
  have ht : t.Finite := hs.biUnion (fun x _ =>
    (isCompact_range (show Continuous (fun g : G => X.ρ g x) from
      hX.comp (continuous_id.prodMk continuous_const))).finite
        (isDiscrete_iff_discreteTopology.mpr inferInstance))
  let W : Submodule R X := Submodule.span R t
  refine ⟨W, ?_, Submodule.fg_span ht, ?_⟩
  · intro x hx
    apply Submodule.subset_span
    apply Set.mem_iUnion.mpr
    refine ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
    refine ⟨1, ?_⟩
    exact congrArg (fun f : X →L[R] X => f x) (map_one X.ρ)
  · intro g
    apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨x, hxUnion⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hxS, hxy⟩ := Set.mem_iUnion.mp hxUnion
    obtain ⟨h, rfl⟩ := hxy
    change X.ρ g (X.ρ h x) ∈ W
    apply Submodule.subset_span
    apply Set.mem_iUnion.mpr
    refine ⟨x, Set.mem_iUnion.mpr ⟨hxS, ?_⟩⟩
    refine ⟨g * h, ?_⟩
    exact congrArg (fun f : X →L[R] X => f x) (map_mul X.ρ g h)

/-- Over a finite scalar ring, the finitely generated invariant submodule
containing a finite set is finite as a type. -/
theorem exists_finite_invariant_submodule [Finite R]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (s : Set X) (hs : s.Finite) :
    ∃ W : Submodule R X, s ⊆ W ∧ Finite W ∧
      ∀ g : G, W ≤ W.comap (X.ρ g).toLinearMap := by
  obtain ⟨W, hsW, hfg, hW⟩ := exists_fg_invariant_submodule R G X hX s hs
  have : Module.Finite R W := Module.Finite.iff_fg.mpr hfg
  exact ⟨W, hsW, Module.finite_of_finite R, hW⟩

/-- Bounded-torsion discrete coefficients over a ring finite as a
Z-module have finite invariant submodules containing every finite set. -/
theorem exists_finite_invariant_submodule_of_annihilator [Module.Finite ℤ R]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ x : X, m • x = 0)
    (s : Set X) (hs : s.Finite) :
    ∃ W : Submodule R X, s ⊆ W ∧ Finite W ∧
      ∀ g : G, W ≤ W.comap (X.ρ g).toLinearMap := by
  obtain ⟨W, hsW, hfg, hW⟩ := exists_fg_invariant_submodule R G X hX s hs
  have : Module.Finite R W := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite ℤ W := Module.Finite.trans R W
  have ht : Module.IsTorsion ℤ W := by
    intro w
    refine ⟨⟨m, mem_nonZeroDivisors_iff_ne_zero.mpr hm0⟩, ?_⟩
    apply Subtype.ext
    exact hm (w : X)
  exact ⟨W, hsW, Module.finite_of_fg_torsion W ht, hW⟩

/-- Continuous cochains from a compact parameter space have their entire
image in one finite invariant coefficient submodule. -/
theorem exists_finite_invariant_submodule_containing_range [Finite R]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    {T : Type*} [TopologicalSpace T] [CompactSpace T] (f : C(T, X)) :
    ∃ W : Submodule R X, Set.range f ⊆ W ∧ Finite W ∧
      ∀ g : G, W ≤ W.comap (X.ρ g).toLinearMap :=
  exists_finite_invariant_submodule R G X hX (Set.range f)
    ((isCompact_range f.continuous).finite
      (isDiscrete_iff_discreteTopology.mpr inferInstance))

end TopRep

namespace TopRep

/-- The kernel of a jointly continuous action on finite discrete coefficients
is open. It is the finite intersection of the point stabilizers. -/
theorem isOpen_finiteCoefficientActionKernel
    (R : Type*) [CommRing R] [TopologicalSpace R]
    (G : Type*) [Group G] [TopologicalSpace G]
    (X : TopRep R G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    IsOpen (X.ρ.toRepresentation.asGroupHom.ker : Set G) := by
  classical
  have heq : (X.ρ.toRepresentation.asGroupHom.ker : Set G) =
      ⋂ x : X, {g : G | X.ρ g x = x} := by
    ext g
    constructor
    · intro hg
      apply Set.mem_iInter.mpr
      intro x
      change X.ρ.toRepresentation.asGroupHom g = 1 at hg
      exact congrArg (fun a : Units (Module.End R X) =>
        (a : Module.End R X) x) hg
    · intro hg
      change X.ρ.toRepresentation.asGroupHom g = 1
      apply Units.ext
      apply LinearMap.ext
      intro x
      exact Set.mem_iInter.mp hg x
  rw [heq]
  apply isOpen_iInter_of_finite
  intro x
  exact (isOpen_discrete ({x} : Set X)).preimage
    (hX.comp (continuous_id.prodMk continuous_const))

end TopRep


namespace TopRep

/-- A finite continuous coefficient action becomes a p-group action after
restriction to an actual open subgroup of index prime to p. -/
theorem exists_openSubgroup_primeToIndex_pGroup_image
    (R : Type*) [CommRing R] [TopologicalSpace R]
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : TopRep R G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (p : ℕ) [Fact p.Prime] :
    ∃ H : OpenSubgroup G, ¬ p ∣ H.toSubgroup.index ∧
      IsPGroup p
        (Representation.asGroupHom (X.ρ.toRepresentation.comp H.toSubgroup.subtype)).range := by
  classical
  let ρ := X.ρ.toRepresentation
  let Q := ρ.asGroupHom.range
  have : Finite (Module.End R X) :=
    Finite.of_injective (fun f : Module.End R X => (f : X → X)) DFunLike.coe_injective
  have : Finite Q := inferInstance
  let : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  let q : G →* Q := ρ.asGroupHom.rangeRestrict
  have hker : q.ker = ρ.asGroupHom.ker := by
    ext g
    change (⟨ρ.asGroupHom g, ⟨g, rfl⟩⟩ : Q) = 1 ↔ ρ.asGroupHom g = 1
    exact Subtype.ext_iff
  have hq : Continuous q :=
    ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete q
      (by rw [hker]; exact isOpen_finiteCoefficientActionKernel R G X hX)
  let P : Sylow p Q := Classical.choice inferInstance
  let PO : OpenSubgroup Q := ⟨P.toSubgroup, isOpen_discrete _⟩
  let H : OpenSubgroup G := PO.comap q hq
  refine ⟨H, ?_, ?_⟩
  · have hidx : H.toSubgroup.index = P.toSubgroup.index :=
      P.toSubgroup.index_comap_of_surjective ρ.asGroupHom.rangeRestrict_surjective
    rw [hidx]
    exact P.not_dvd_index
  · have hP : IsPGroup p (P.toSubgroup.map Q.subtype) := P.isPGroup'.map Q.subtype
    have hle :
        (Representation.asGroupHom (ρ.comp H.toSubgroup.subtype)).range ≤
          P.toSubgroup.map Q.subtype := by
      rintro a ⟨g, rfl⟩
      exact ⟨q g, g.property, rfl⟩
    exact hP.of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)

end TopRep
