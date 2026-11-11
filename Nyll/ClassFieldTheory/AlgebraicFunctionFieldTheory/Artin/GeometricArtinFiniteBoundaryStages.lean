/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinBoundaryStages

/-!
# Simultaneous descent of finite geometric boundary families

An actual finite family of geometric places becomes pairwise distinct at
one finite constant stage and remains distinct at every larger stage. The
argument uses the original valuation-ring restrictions, one pair at a time.
Reduced boundary exponents descend through the same original inclusions.
-/

@[expose] public section


noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

local notation "E" => geometricArtinStageField k K Ω
local notation "G" => geometricConstantExtension k K Ω
local notation "C" => separableClosure k Ω

attribute [local instance]
  geometricBoundaryConstants geometricBoundaryConstantTower

private theorem exists_stage_separating_pairs
    (i : GeometricArtinIndex k K Ω) (s : Finset (Place C G × Place C G)) :
    ∃ j : GeometricArtinIndex k K Ω, i ≤ j ∧
      ∀ l : GeometricArtinIndex k K Ω, j ≤ l →
      ∀ W V : Place C G, (W, V) ∈ s → W ≠ V →
        geometricArtinPlaceAtStage k K Ω l W ≠
          geometricArtinPlaceAtStage k K Ω l V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨i, le_rfl, ?_⟩
      intro l _ W V hmem
      exact False.elim (Finset.notMem_empty (W, V) hmem)
  | @insert a s _ha ih =>
      obtain ⟨j, hij, hj⟩ := ih
      by_cases hsame : a.1 = a.2
      · refine ⟨j, hij, ?_⟩
        intro l hjl W V hmem hne
        rcases Finset.mem_insert.mp hmem with heq | hs
        · exact False.elim (hne ((congrArg Prod.fst heq).trans
            (hsame.trans (congrArg Prod.snd heq).symm)))
        · exact hj l hjl W V hs hne
      · obtain ⟨j', hjj', hsep⟩ :=
          exists_geometricArtinStage_separating k K Ω j a.1 a.2 hsame
        refine ⟨j', hij.trans hjj', ?_⟩
        intro l hj'l W V hmem hne
        rcases Finset.mem_insert.mp hmem with heq | hs
        · have hW : W = a.1 := congrArg Prod.fst heq
          have hV : V = a.2 := congrArg Prod.snd heq
          rw [hW, hV]
          intro h
          exact hsep
            (geometricArtinPlaceAtStage_eq_of_le k K Ω j' l hj'l a.1 a.2 h)
        · exact hj l (hjj'.trans hj'l) W V hs hne

/-- Every finite injective family of actual geometric places has a
cofinal collection of finite constant stages with injective restriction. -/
theorem exists_geometricArtinStage_separating_finite
    {ι : Type*} [Finite ι] (W : ι → Place C G) (hW : Function.Injective W)
    (i : GeometricArtinIndex k K Ω) :
    ∃ j : GeometricArtinIndex k K Ω, i ≤ j ∧
      ∀ l : GeometricArtinIndex k K Ω, j ≤ l →
        Function.Injective (fun a => geometricArtinPlaceAtStage k K Ω l (W a)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let s : Finset (Place C G × Place C G) :=
    Finset.univ.image (fun a : ι × ι => (W a.1, W a.2))
  obtain ⟨j, hij, hj⟩ := exists_stage_separating_pairs k K Ω i s
  refine ⟨j, hij, ?_⟩
  intro l hjl a b hab
  by_contra hne
  have hmem : (W a, W b) ∈ s :=
    Finset.mem_image_of_mem _ (Finset.mem_univ (a, b))
  exact hj l hjl (W a) (W b) hmem (fun h => hne (hW h)) hab

/-- A finite family with at least two actual geometric boundary places
descends injectively and with its original exponent one at all sufficiently
large stages. Every place at each such stage has another boundary place. -/
theorem exists_geometricArtinStage_separating_boundary_finite
    (m : Modulus k K) {ι : Type*} [Finite ι]
    (W : ι → Place C G) (hW : Function.Injective W)
    (hboundary : ∀ a, m (algebraicConstantPlaceRestrict (K := K) C K (W a)) = 1)
    (a b : ι) (hab : a ≠ b) (i : GeometricArtinIndex k K Ω) :
    ∃ j : GeometricArtinIndex k K Ω, i ≤ j ∧
      ∀ l : GeometricArtinIndex k K Ω, j ≤ l →
        Function.Injective (fun t => geometricArtinPlaceAtStage k K Ω l (W t)) ∧
        (∀ t, rayModulusBaseChange (E l) m
          (geometricArtinPlaceAtStage k K Ω l (W t)) = 1) ∧
        ∀ v : Place k (E l), ∃ w : Place k (E l),
          w ≠ v ∧ rayModulusBaseChange (E l) m w ≠ 0 := by
  obtain ⟨j, hij, hsep⟩ := exists_geometricArtinStage_separating_finite k K Ω W hW i
  have ha : m (algebraicConstantPlaceRestrict (K := K) C K (W a)) ≠ 0 := by
    rw [hboundary a]
    exact Nat.one_ne_zero
  have hb : m (algebraicConstantPlaceRestrict (K := K) C K (W b)) ≠ 0 := by
    rw [hboundary b]
    exact Nat.one_ne_zero
  obtain ⟨j', hjj', hgood⟩ := exists_geometricArtinStage_other_boundary
    k K Ω m j (W a) (W b) (fun h => hab (hW h)) ha hb
  refine ⟨j', hij.trans hjj', ?_⟩
  intro l hj'l
  refine ⟨hsep l (hjj'.trans hj'l), ?_, hgood l hj'l⟩
  intro t
  rw [geometricArtinPlaceAtStage_modulus]
  exact hboundary t

end FunctionField.RayClass
