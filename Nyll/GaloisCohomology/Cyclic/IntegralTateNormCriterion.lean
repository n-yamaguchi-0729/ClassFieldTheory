/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Coinvariants
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.TateComparison

/-!
# The norm criteria in degrees zero and minus one

The two original Tate groups measure surjectivity and injectivity of the
finite norm from coinvariants to invariants. The criteria use the original
module and acting group, including the full span of all action differences.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- Vanishing in degree zero means every original invariant is a norm. -/
theorem tateZero_isZero_iff_norm_surjective (A : Rep.{v} ℤ G) :
    IsZero (tate A 0) ↔ ∀ x : A.ρ.invariants, ∃ y : A, A.ρ.norm y = x.val := by
  constructor
  · intro h x
    have : Subsingleton (tate A 0) := ModuleCat.subsingleton_of_isZero h
    have hclass : fixedClass A x = 0 := Subsingleton.elim _ _
    have hz : (fixedNormSubmodule A).mkQ x = 0 := by
      rw [← tateZeroEquivFixedQuotient_fixedClass, hclass, map_zero]
    exact (Submodule.Quotient.mk_eq_zero (fixedNormSubmodule A)).mp hz
  · intro h
    have hz (x : tate A 0) : x = 0 := by
      obtain ⟨a, rfl⟩ := fixedClass_surjective A x
      apply (tateZeroEquivFixedQuotient A).injective
      rw [tateZeroEquivFixedQuotient_fixedClass, map_zero]
      exact (Submodule.Quotient.mk_eq_zero (fixedNormSubmodule A)).mpr (h a)
    have : Subsingleton (tate A 0) := ⟨fun x y => (hz x).trans (hz y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _

omit [Fintype G] in
private theorem nativeCoinvariantsKer_iff (A : Rep.{v} ℤ G) (x : A) :
    ULift.up x ∈ Representation.Coinvariants.ker ((nativeFunctor G).obj A).ρ ↔
      x ∈ Representation.Coinvariants.ker A.ρ := by
  let M := (nativeFunctor G).obj A
  let down : M → A := fun z => (show ULift.{u} A from z).down
  constructor
  · intro hx
    have h (z : M) (hz : z ∈ Representation.Coinvariants.ker M.ρ) :
        down z ∈ Representation.Coinvariants.ker A.ρ := by
      change z ∈ Submodule.span _ (Set.range fun gz : ULift.{v} G × M => M.ρ gz.1 gz.2 - gz.2) at hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨⟨g, y⟩, rfl⟩ := hz
        change A.ρ g.down (down y) - down y ∈ Representation.Coinvariants.ker A.ρ
        exact Representation.Coinvariants.sub_mem_ker g.down (down y)
      | zero => exact (Representation.Coinvariants.ker A.ρ).zero_mem
      | add y z _ _ hy hz => exact (Representation.Coinvariants.ker A.ρ).add_mem hy hz
      | smul n z _ hz => exact (Representation.Coinvariants.ker A.ρ).smul_mem n.down hz
    exact h (ULift.up x) hx
  · intro hx
    change x ∈ Submodule.span ℤ (Set.range fun gx : G × A => A.ρ gx.1 gx.2 - gx.2) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, y⟩, rfl⟩ := hx
      exact Representation.Coinvariants.sub_mem_ker (ρ := M.ρ) (ULift.up g) (ULift.up y)
    | zero => exact (Representation.Coinvariants.ker M.ρ).zero_mem
    | add y z _ _ hy hz => exact (Representation.Coinvariants.ker M.ρ).add_mem hy hz
    | smul n z _ hz => exact (Representation.Coinvariants.ker M.ρ).smul_mem (ULift.up n) hz

/-- Vanishing in degree minus one means every original norm-zero vector
belongs to the span of the original action differences. -/
theorem tateNegOne_isZero_iff_norm_kernel (A : Rep.{v} ℤ G) :
    IsZero (tate A (-1)) ↔
      ∀ x : A, A.ρ.norm x = 0 → x ∈ Representation.Coinvariants.ker A.ρ := by
  let M := (nativeFunctor G).obj A
  let S := ShortComplex.mk (groupHomology.d₁₀ M) M.norm.asHom.toModuleCatHom (Rep.comp_eq_zero M)
  constructor
  · intro h x hx
    have : Subsingleton (tateCohomology M (-1)) :=
      ModuleCat.subsingleton_of_isZero (M := tate A (-1)) h
    have hn : IsZero (tateCohomology M (-1)) := ModuleCat.isZero_of_subsingleton _
    have he : S.Exact := S.exact_iff_isZero_homology.mpr
      (hn.of_iso (TateCohomology.isoNegOneBoundary M).symm)
    let z : S.X₂ := ULift.up x
    have hz : S.g z = 0 := ULift.down_injective ((nativeFunctor_norm_down A x).trans hx)
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp he z hz
    let w := groupHomology.chains₁ToCoinvariantsKer M y
    have hw : w.val = ULift.up x := hy
    exact (nativeCoinvariantsKer_iff A x).mp (hw ▸ w.property)
  · intro h
    have he : S.Exact := (ShortComplex.moduleCat_exact_iff S).mpr (by
      intro z hz
      let x : A := (show ULift.{u} A from z).down
      have hx : A.ρ.norm x = 0 :=
        (nativeFunctor_norm_down A x).symm.trans (congrArg ULift.down hz)
      have hker : z ∈ Representation.Coinvariants.ker M.ρ :=
        (nativeCoinvariantsKer_iff A x).mpr (h x hx)
      obtain ⟨y, hy⟩ := groupHomology.chains₁ToCoinvariantsKer_surjective M ⟨z, hker⟩
      exact ⟨y, congrArg Subtype.val hy⟩)
    have hn : IsZero (tateCohomology M (-1)) :=
      (S.exact_iff_isZero_homology.mp he).of_iso (TateCohomology.isoNegOneBoundary M)
    have : Subsingleton (tate A (-1)) :=
      ModuleCat.subsingleton_of_isZero (M := tateCohomology M (-1)) hn
    exact ModuleCat.isZero_of_subsingleton _

end IntegralGroupCohomology.Universe
