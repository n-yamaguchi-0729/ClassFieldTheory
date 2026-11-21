/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Tactic.Abel

/-! # Descent of degree-two coboundaries through a quotient -/

@[expose] public section

open CategoryTheory groupCohomology Rep

noncomputable section
namespace ClassFieldTower.Cohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- If subgroup first cohomology vanishes, an upstairs primitive of an
inflated two-cocycle can be corrected to descend to the quotient. -/
theorem degreeTwo_inflation_injective
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (groupCohomology (Rep.res S.subtype A) 1)] :
    Function.Injective ((groupCohomology.infNatTrans k S 2).app A).hom := by
  apply (AddMonoidHom.ker_eq_bot_iff
    ((groupCohomology.infNatTrans k S 2).app A).hom.toAddMonoidHom).mp
  apply bot_unique
  intro x hx
  change x = 0
  induction x using H2_induction_on with
  | h c =>
    let B := A.quotientToInvariants S
    change cocycles₂ B at c
    let q := QuotientGroup.mk' S
    let i : Rep.res q B ⟶ A := Rep.ofHom (A.ρ.quotientToInvariants_lift S)
    change groupCohomology.map q i 2 (H2π B c) = 0 at hx
    rw [H2π_comp_map_apply] at hx
    obtain ⟨b, hb⟩ := (H2π_eq_zero_iff _).mp hx
    have hdb (g h : G) : A.ρ g (b h) - b (g * h) + b g = (c (q g, q h) : A) :=
      congrFun hb (g, h)
    have hb1 : b 1 = (c (1, 1) : A) := by
      simpa only [map_one, one_apply_eq_self, one_mul, sub_self, zero_add] using hdb 1 1
    have hq (n : S) : q n = 1 := (QuotientGroup.eq_one_iff (n : G)).mpr n.property
    let D := Rep.res S.subtype A
    let z : cocycles₁ D := ⟨fun n => b n - b 1, (mem_cocycles₁_def _).mpr (fun m n => by
      have h := hdb m n
      rw [hq m, hq n, ← hb1] at h
      have hfixed : A.ρ (m : G) (b 1) = b 1 := by
        rw [hb1]
        exact (c (1, 1)).property m
      change A.ρ (m : G) (b n - b 1) - (b ((m : G) * n) - b 1) + (b m - b 1) = 0
      rw [map_sub, hfixed]
      calc
        _ = (A.ρ (m : G) (b n) - b (m * n) + b m) - b 1 := by abel
        _ = 0 := sub_eq_zero.mpr h)⟩
    obtain ⟨a, ha⟩ := (H1π_eq_zero_iff z).mp (Subsingleton.elim (H1π D z) 0)
    let b' := b - (d₀₁ A).hom a
    have hdb' (g h : G) : A.ρ g (b' h) - b' (g * h) + b' g = (c (q g, q h) : A) := by
      have hz := d₀₁_comp_d₁₂_apply A a
      change (d₁₂ A).hom ((d₀₁ A).hom a) = 0 at hz
      have he : (d₁₂ A).hom b' = (d₁₂ A).hom b := by
        change (d₁₂ A).hom (b - (d₀₁ A).hom a) = _
        rw [map_sub, hz, sub_zero]
      exact (congrFun he (g, h)).trans (hdb g h)
    have hS (n : S) : b' n = b 1 := by
      change b n - (A.ρ (n : G) a - a) = b 1
      have h : A.ρ (n : G) a - a = b n - b 1 := congrFun ha n
      rw [h]
      abel
    have hright (g : G) (n : S) : b' (g * n) = b' g := by
      have h := hdb' g n
      rw [hS n, hq n, cocycles₂_map_one_snd] at h
      change A.ρ g (b 1) - b' (g * n) + b' g = A.ρ g (c (1, 1) : A) at h
      rw [← hb1] at h
      symm
      apply add_left_cancel (a := A.ρ g (b 1))
      calc
        _ = (A.ρ g (b 1) - b' (g * n) + b' g) + b' (g * n) := by abel
        _ = _ := congrArg (· + b' (g * n)) h
    have hinvariant (g : G) (n : S) : A.ρ (n : G) (b' g) = b' g := by
      let m : S := ⟨g⁻¹ * (n : G) * g,
        Subgroup.Normal.conj_mem' inferInstance n.val n.property g⟩
      have hmul : g * (m : G) = (n : G) * g := by
        dsimp only [m]
        rw [mul_assoc, mul_inv_cancel_left]
      have h := hdb' n g
      rw [← hmul, hright, hS n, hq n, cocycles₂_map_one_fst, ← hb1] at h
      exact sub_eq_zero.mp (add_right_cancel (h.trans (zero_add (b 1)).symm))
    let s := Function.surjInv (QuotientGroup.mk'_surjective S)
    let d (x : G ⧸ S) : B := ⟨b' (s x), hinvariant (s x)⟩
    have hd (g : G) : (d (q g) : A) = b' g := by
      let n : S := ⟨g⁻¹ * s (q g), (QuotientGroup.eq_one_iff _).mp (by
        change q (g⁻¹ * s (q g)) = 1
        rw [map_mul, map_inv, Function.surjInv_eq (QuotientGroup.mk'_surjective S),
          inv_mul_cancel])⟩
      have hmul : g * (n : G) = s (q g) := mul_inv_cancel_left _ _
      exact (congrArg b' hmul).symm.trans (hright g n)
    apply (H2π_eq_zero_iff c).mpr
    refine ⟨d, ?_⟩
    funext xy
    rcases xy with ⟨x, y⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective S y
    apply Subtype.ext
    change A.ρ g (d (q h) : A) - (d (q g * q h) : A) + (d (q g) : A) = (c (q g, q h) : A)
    rw [← map_mul q, hd, hd, hd]
    exact hdb' g h

/-- An inflated class restricts to zero, using the constant primitive of
its restriction to the subgroup. -/
theorem degreeTwo_restrict_inflate_eq_zero (A : Rep k G) (S : Subgroup G) [S.Normal]
    (x : H2 (A.quotientToInvariants S)) :
    groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2
      (((groupCohomology.infNatTrans k S 2).app A).hom x) = 0 := by
  induction x using H2_induction_on with
  | h c =>
    let q := QuotientGroup.mk' S
    let i := Rep.ofHom (A.ρ.quotientToInvariants_lift S)
    change groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2
      (groupCohomology.map q i 2 (H2π (A.quotientToInvariants S) c)) = 0
    rw [H2π_comp_map_apply, H2π_comp_map_apply]
    apply (H2π_eq_zero_iff _).mpr
    refine ⟨fun _ => (c (1, 1) : A), ?_⟩
    funext xy
    rcases xy with ⟨a, b⟩
    have hq (n : S) : q n = 1 := (QuotientGroup.eq_one_iff (n : G)).mpr n.property
    have hfixed : A.ρ (a : G) (c (1, 1) : A) = (c (1, 1) : A) := (c (1, 1)).property a
    change A.ρ (a : G) (c (1, 1) : A) - (c (1, 1) : A) + (c (1, 1) : A) =
      (c (q a, q b) : A)
    rw [hq a, hq b, hfixed, sub_self, zero_add]

end ClassFieldTower.Cohomology
