/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

The same diagram proof also occurs in the fppf-quotient source pinned at:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_fppf_quotient_of_forall_exists_quotient_restrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Cocycle identity for quotient overlap maps

The diagram proof depends on the actual quotient charts, overlap maps and their
compatibilities. It does not choose charts from existence certificates.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.QuotGlue

/-- Compatible overlap maps satisfy the gluing cocycle after cancellation along
the actual restricted quotient morphism. -/
theorem overlap_cocycle
    {I : Type v} {X : Scheme.{u}}
    (W : I → X.Opens) (Y : I → Scheme.{u})
    (p : ∀ i, (W i).toScheme ⟶ Y i)
    (V : ∀ i, I → (Y i).Opens)
    (eX : ∀ i j, (p i ⁻¹ᵁ V i j : Scheme.{u}) ≅ (p j ⁻¹ᵁ V j i : Scheme.{u}))
    (φ : ∀ i j, (V i j : Scheme.{u}) ≅ (V j i : Scheme.{u}))
    (hpreimage : ∀ i j, p i ⁻¹ᵁ V i j = (W i).ι ⁻¹ᵁ W j)
    (heX : ∀ i j, (eX i j).hom ≫ Scheme.Opens.ι _ ≫ (W j).ι =
      Scheme.Opens.ι _ ≫ (W i).ι)
    (hφ : ∀ i j, (p i ∣_ V i j) ≫ (φ i j).hom = (eX i j).hom ≫ (p j ∣_ V j i))
    (hepi : ∀ i j (O : (V i j : Scheme.{u}).Opens), Epi ((p i ∣_ V i j) ∣_ O))
    (hinter : ∀ i j k, (V i j).ι ⁻¹ᵁ V i k ≤
      (φ i j).hom ⁻¹ᵁ ((V j i).ι ⁻¹ᵁ V j k))
    (x y z : I) :
    ((φ x y).hom.resLE ((V y x).ι ⁻¹ᵁ (V y z))
        ((V x y).ι ⁻¹ᵁ (V x z)) (hinter x y z) ≫
      ((Y y).restrictRestrictComm (V y x)
          (V y z)).hom ≫
        ((V y z).ι ⁻¹ᵁ (V y x)).ι ≫
          (φ y z).hom ≫ (V z y).ι) =
    ((Y x).restrictRestrictComm (V x y)
        (V x z)).hom ≫
      ((V x z).ι ⁻¹ᵁ (V x y)).ι ≫
        (φ x z).hom ≫ (V z x).ι := by
  set O : (V x y : Scheme.{u}).Opens :=
    (V x y).ι ⁻¹ᵁ (V x z) with hO
  have : Epi ((p x ∣_ V x y) ∣_ O) := hepi x y O
  rw [← cancel_epi ((p x ∣_ V x y) ∣_ O)]
  have hQ : ((p x ∣_ V x y) ∣_ O) ≫ O.ι =
      ((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ∣_ V x y) := morphismRestrict_ι _ _
  have hmem : ∀ u : ↑((p x ∣_ V x y) ⁻¹ᵁ O),
      (((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ⁻¹ᵁ V x y).ι) u ∈
        p x ⁻¹ᵁ V x z := by
    intro u
    have h1 : ((p x ∣_ V x y) ⁻¹ᵁ O).ι u ∈
        (((p x ∣_ V x y) ⁻¹ᵁ O : (_ : Scheme.{u}).Opens) : Set _) :=
      (Scheme.Opens.range_ι _).le ⟨u, rfl⟩
    have h2 : ((((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ∣_ V x y) ≫ (V x y).ι) u) ∈
        V x z := h1
    rw [morphismRestrict_ι] at h2
    exact h2
  have hmemW : ∀ u : ↑((p x ∣_ V x y) ⁻¹ᵁ O),
      (((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ⁻¹ᵁ V x y).ι ≫ (W x).ι) u ∈
        W z := by
    intro u
    have := hmem u
    rw [hpreimage] at this
    exact this
  let lam₁ : ((p x ∣_ V x y) ⁻¹ᵁ O : Scheme.{u}) ⟶ (p x ⁻¹ᵁ V x z) :=
    IsOpenImmersion.lift (p x ⁻¹ᵁ V x z).ι
      (((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ⁻¹ᵁ V x y).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmem u)
  have hlam₁ : lam₁ ≫ (p x ⁻¹ᵁ V x z).ι =
      ((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ⁻¹ᵁ V x y).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let kap : ((p x ∣_ V x y) ⁻¹ᵁ O : Scheme.{u}) ⟶ (W z : Scheme.{u}) :=
    IsOpenImmersion.lift (W z).ι
      (((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ⁻¹ᵁ V x y).ι ≫ (W x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmemW u)
  have hkap : kap ≫ (W z).ι =
      ((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (p x ⁻¹ᵁ V x y).ι ≫ (W x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let lam₂ : ((p x ∣_ V x y) ⁻¹ᵁ O : Scheme.{u}) ⟶ (p y ⁻¹ᵁ V y z) :=
    IsOpenImmersion.lift (p y ⁻¹ᵁ V y z).ι
      (((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (eX x y).hom ≫
        (p y ⁻¹ᵁ V y x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        change _ ∈ p y ⁻¹ᵁ V y z
        rw [hpreimage]
        change ((((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (eX x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
        rw [heX]
        exact hmemW u)
  have hlam₂ : lam₂ ≫ (p y ⁻¹ᵁ V y z).ι =
      ((p x ∣_ V x y) ⁻¹ᵁ O).ι ≫ (eX x y).hom ≫
        (p y ⁻¹ᵁ V y x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have σx : ((Y x).restrictRestrictComm (V x y)
      (V x z)).hom ≫ ((V x z).ι ⁻¹ᵁ V x y).ι ≫
        (V x z).ι = O.ι ≫ (V x y).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have σy : ((Y y).restrictRestrictComm (V y x)
      (V y z)).hom ≫ ((V y z).ι ⁻¹ᵁ V y x).ι ≫
        (V y z).ι =
      ((V y x).ι ⁻¹ᵁ V y z).ι ≫ (V y x).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have R1 : ((p x ∣_ V x y) ∣_ O) ≫ ((Y x).restrictRestrictComm (V x y)
      (V x z)).hom ≫ ((V x z).ι ⁻¹ᵁ V x y).ι =
      lam₁ ≫ (p x ∣_ V x z) := by
    rw [← cancel_mono (V x z).ι]
    simp only [Category.assoc]
    rw [σx, reassoc_of% hQ, morphismRestrict_ι (p x) (V x y),
      morphismRestrict_ι (p x) (V x z), reassoc_of% hlam₁]
  have R3 : lam₁ ≫ (eX x z).hom ≫ (p z ⁻¹ᵁ V z x).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [heX, reassoc_of% hlam₁, hkap]
  have R : ((p x ∣_ V x y) ∣_ O) ≫ ((Y x).restrictRestrictComm (V x y)
      (V x z)).hom ≫ ((V x z).ι ⁻¹ᵁ V x y).ι ≫
        (φ x z).hom ≫ (V z x).ι = kap ≫ p z := by
    rw [reassoc_of% R1, reassoc_of% (hφ x z),
      morphismRestrict_ι (p z) (V z x), reassoc_of% R3]
  have L1 : ((p x ∣_ V x y) ∣_ O) ≫
      (φ x y).hom.resLE ((V y x).ι ⁻¹ᵁ (V y z)) O
        (hinter x y z) ≫
      ((Y y).restrictRestrictComm (V y x)
          (V y z)).hom ≫ ((V y z).ι ⁻¹ᵁ V y x).ι =
      lam₂ ≫ (p y ∣_ V y z) := by
    rw [← cancel_mono (V y z).ι]
    simp only [Category.assoc]
    rw [σy, Scheme.Hom.resLE_comp_ι_assoc, reassoc_of% hQ, reassoc_of% (hφ x y),
      morphismRestrict_ι (p y) (V y x),
      morphismRestrict_ι (p y) (V y z), reassoc_of% hlam₂]
  have L3 : lam₂ ≫ (eX y z).hom ≫ (p z ⁻¹ᵁ V z y).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [heX, reassoc_of% hlam₂, heX, hkap]
  have L : ((p x ∣_ V x y) ∣_ O) ≫
      (φ x y).hom.resLE ((V y x).ι ⁻¹ᵁ (V y z)) O
        (hinter x y z) ≫
      ((Y y).restrictRestrictComm (V y x)
          (V y z)).hom ≫ ((V y z).ι ⁻¹ᵁ V y x).ι ≫
        (φ y z).hom ≫ (V z y).ι = kap ≫ p z := by
    rw [reassoc_of% L1, reassoc_of% (hφ y z),
      morphismRestrict_ι (p z) (V z y), reassoc_of% L3]
  rw [L, R]

end AlgebraicGeometry.Scheme.QuotGlue
