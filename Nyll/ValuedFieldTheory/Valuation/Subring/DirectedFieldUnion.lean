/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Order.Directed

/-!
# Compatible valuation rings on a directed union of fields

The valuation ring on the union is constructed as the union of the original
valuation rings through their literal field inclusions. Its pullback to each
stage is exactly the specified valuation ring. In particular, nontriviality at
one stage implies nontriviality on the union.
-/

@[expose] public section

noncomputable section

namespace ValuationSubring

variable {B Ω : Type*} [Field B] [Field Ω] [Algebra B Ω]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (E : ι → IntermediateField B Ω) (hE : Monotone E)
    (G : IntermediateField B Ω) (hEG : ∀ i, E i ≤ G)
    (hex : ∀ x : G, ∃ i, (x : Ω) ∈ E i)
    (V : ∀ i, ValuationSubring (E i))
    (hV : ∀ (i j : ι) (hij : i ≤ j) (x : E i),
      IntermediateField.inclusion (hE hij) x ∈ V j ↔ x ∈ V i)

/-- The valuation ring obtained from the original rings at every finite
stage of a directed field union. -/
def directedFieldUnion : ValuationSubring G where
  carrier := {z | ∃ (i : ι) (x : E i), x ∈ V i ∧ (x : Ω) = (z : Ω)}
  zero_mem' := ⟨Classical.arbitrary ι, 0, (V _).zero_mem, rfl⟩
  one_mem' := ⟨Classical.arbitrary ι, 1, (V _).one_mem, rfl⟩
  add_mem' := by
    rintro x y ⟨i, a, ha, hax⟩ ⟨j, b, hb, hby⟩
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    let a' : E l := IntermediateField.inclusion (hE hil) a
    let b' : E l := IntermediateField.inclusion (hE hjl) b
    refine ⟨l, a' + b', (V l).add_mem a' b'
      ((hV i l hil a).mpr ha) ((hV j l hjl b).mpr hb), ?_⟩
    change (a : Ω) + (b : Ω) = (x : Ω) + (y : Ω)
    rw [hax, hby]
  neg_mem' := by
    rintro x ⟨i, a, ha, hax⟩
    refine ⟨i, -a, (V i).neg_mem a ha, ?_⟩
    change -(a : Ω) = -(x : Ω)
    exact congrArg Neg.neg hax
  mul_mem' := by
    rintro x y ⟨i, a, ha, hax⟩ ⟨j, b, hb, hby⟩
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    let a' : E l := IntermediateField.inclusion (hE hil) a
    let b' : E l := IntermediateField.inclusion (hE hjl) b
    refine ⟨l, a' * b', (V l).mul_mem a' b'
      ((hV i l hil a).mpr ha) ((hV j l hjl b).mpr hb), ?_⟩
    change (a : Ω) * (b : Ω) = (x : Ω) * (y : Ω)
    rw [hax, hby]
  mem_or_inv_mem' := by
    intro x
    obtain ⟨i, hi⟩ := hex x
    let a : E i := ⟨(x : Ω), hi⟩
    rcases (V i).mem_or_inv_mem a with ha | ha
    · exact Or.inl ⟨i, a, ha, rfl⟩
    · exact Or.inr ⟨i, a⁻¹, ha, rfl⟩

/-- Membership of an original stage element is unchanged by passing to
the directed union valuation ring. -/
theorem directedFieldUnion_mem_inclusion (i : ι) (x : E i) :
    IntermediateField.inclusion (hEG i) x ∈
        directedFieldUnion E hE G hex V hV ↔ x ∈ V i := by
  constructor
  · rintro ⟨j, y, hy, hyx⟩
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    have heq : IntermediateField.inclusion (hE hil) x =
        IntermediateField.inclusion (hE hjl) y := Subtype.ext hyx.symm
    apply (hV i l hil x).mp
    rw [heq]
    exact (hV j l hjl y).mpr hy
  · intro hx
    exact ⟨i, x, hx, rfl⟩

/-- The constructed ring restricts to the original ring at every stage. -/
theorem directedFieldUnion_comap (i : ι) :
    (directedFieldUnion E hE G hex V hV).comap
        (IntermediateField.inclusion (hEG i)).toRingHom = V i := by
  apply SetLike.ext
  intro x
  exact directedFieldUnion_mem_inclusion E hE G hEG hex V hV i x

include hEG in
/-- A proper original stage ring prevents the union valuation ring from
becoming the whole field. -/
theorem directedFieldUnion_ne_top (i : ι) (hi : V i ≠ ⊤) :
    directedFieldUnion E hE G hex V hV ≠ ⊤ := by
  intro htop
  apply hi
  apply SetLike.ext
  intro x
  constructor
  · intro _
    exact mem_top x
  · intro _
    apply (directedFieldUnion_mem_inclusion E hE G hEG hex V hV i x).mp
    rw [htop]
    exact mem_top _

/-- The specified pullbacks determine the valuation ring on the union
uniquely; no choice of finite representative affects it. -/
theorem directedFieldUnion_unique (A : ValuationSubring G)
    (hA : ∀ (i : ι) (x : E i),
      IntermediateField.inclusion (hEG i) x ∈ A ↔ x ∈ V i) :
    A = directedFieldUnion E hE G hex V hV := by
  apply SetLike.ext
  intro x
  obtain ⟨i, hi⟩ := hex x
  let a : E i := ⟨(x : Ω), hi⟩
  have ha : IntermediateField.inclusion (hEG i) a = x := Subtype.ext rfl
  rw [← ha, hA, directedFieldUnion_mem_inclusion E hE G hEG hex V hV]

end ValuationSubring
