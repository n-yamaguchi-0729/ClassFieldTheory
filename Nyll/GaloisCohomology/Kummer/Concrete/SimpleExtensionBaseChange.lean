/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteGeneration

public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.GaloisCohomology.Topology.SeparableGaloisMap

/-!
# Embedding the actual simple Kummer extensions after base change

The image of a chosen radical differs from the radical chosen over the new
base by a root of unity in that base. Thus the original simple extension
embeds into the new one, without a normality assumption on the base change.
-/

@[expose] public section

namespace KummerTheory

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The chosen simple Kummer extension embeds into the chosen simple extension
of the same radical over any larger field containing the roots of unity. -/
theorem chosenSimpleKummerExtension_baseChange_nonempty
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hnL : ((n : ℕ) : L) ≠ 0)
    (hmuL : (primitiveRoots (n : ℕ) L).Nonempty) (b : Kˣ) :
    let F := chosenSimpleKummerExtension L n hnL
      (Units.map (algebraMap K L).toMonoidHom b)
    let : Algebra K F := ((algebraMap L F).comp (algebraMap K L)).toAlgebra
    Nonempty (chosenSimpleKummerExtension K n hnK b →ₐ[K] F) := by
  intro F sharedAlgebra
  let E := chosenSimpleKummerExtension K n hnK b
  let bL : Lˣ := Units.map (algebraMap K L).toMonoidHom b
  let j := Field.absoluteGaloisGroup.separableClosureLift (algebraMap K L)
  let alpha : (SeparableClosure L)ˣ :=
    Units.map j.toMonoidHom
      (Units.map E.val.toMonoidHom (chosenSimpleKummerRootUnit K n hnK b))
  let beta : (SeparableClosure L)ˣ :=
    Units.map F.val.toMonoidHom (chosenSimpleKummerRootUnit L n hnL bL)
  have halpha : alpha ^ (n : ℕ) =
      Units.map (algebraMap L (SeparableClosure L)).toMonoidHom bL := by
    apply Units.ext
    change j (chosenSimpleKummerRoot K n hnK b) ^ (n : ℕ) =
      algebraMap L (SeparableClosure L) (algebraMap K L (b : K))
    rw [← map_pow, chosenSimpleKummerRoot_pow]
    exact Field.absoluteGaloisGroup.separableClosureLift_algebraMap
      (algebraMap K L) (b : K)
  have hbeta : beta ^ (n : ℕ) =
      Units.map (algebraMap L (SeparableClosure L)).toMonoidHom bL := by
    apply Units.ext
    exact chosenSimpleKummerRoot_pow L n hnL bL
  have hratio : (alpha / beta) ^ (n : ℕ) = 1 := by
    exact div_pow_eq_one_of_pow_eq_pow (halpha.trans hbeta.symm)
  obtain ⟨zeta, hzeta⟩ := nthRootsOfUnityInBase_of_primitiveRoots
    (K := L) (L := SeparableClosure L) n hmuL (alpha / beta) hratio
  have hroot : j (chosenSimpleKummerRoot K n hnK b) ∈ F := by
    have hmul : alpha =
        Units.map (algebraMap L (SeparableClosure L)).toMonoidHom zeta * beta := by
      rw [hzeta, div_mul_cancel]
    have hval := congrArg (fun x : (SeparableClosure L)ˣ => (x : SeparableClosure L))
      hmul
    change j (chosenSimpleKummerRoot K n hnK b) =
      algebraMap L (SeparableClosure L) (zeta : L) *
        chosenSimpleKummerRoot L n hnL bL at hval
    rw [hval]
    exact F.mul_mem (F.algebraMap_mem (zeta : L))
      (IntermediateField.subset_adjoin L _ (Set.mem_singleton _))
  have hmem' (x : SeparableClosure K)
      (hx : x ∈ IntermediateField.adjoin K {chosenSimpleKummerRoot K n hnK b}) :
      j x ∈ F := by
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        have hy' := Set.mem_singleton_iff.mp hy
        subst y
        exact hroot
    | algebraMap a =>
        rw [Field.absoluteGaloisGroup.separableClosureLift_algebraMap]
        exact F.algebraMap_mem (algebraMap K L a)
    | add x y hx hy ihx ihy =>
        rw [map_add]
        exact F.add_mem ihx ihy
    | inv x hx ihx =>
        rw [map_inv₀]
        exact F.inv_mem ihx
    | mul x y hx hy ihx ihy =>
        rw [map_mul]
        exact F.mul_mem ihx ihy
  have hmem (x : E) : j (x : SeparableClosure K) ∈ F := hmem' x x.property
  refine ⟨{ toRingHom := (j.comp E.val.toRingHom).codRestrict F hmem
            commutes' := ?_ }⟩
  intro a
  apply Subtype.ext
  exact Field.absoluteGaloisGroup.separableClosureLift_algebraMap (algebraMap K L) a

end KummerTheory
