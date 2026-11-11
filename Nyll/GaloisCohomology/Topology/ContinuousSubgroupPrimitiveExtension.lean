/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RightQuotient
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Tactic.Abel

/-!
# Extending a continuous degree-two primitive from an open subgroup

The existing normalized continuous coset retraction extends a subgroup
primitive. The prism correction makes its boundary equal to the original
ambient homogeneous cocycle.
-/

@[expose] public section

noncomputable section
open scoped Topology
open ReidemeisterSchreier.Profinite

namespace ContinuousCohomology

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]

/-- The continuous extension of a subgroup primitive with its prism correction. -/
def openSubgroupPrimitiveExtension (H : OpenSubgroup G)
    [LocallyCompactSpace ↥(H : Subgroup G)]
    (z : C(G, C(G, C(G, M))))
    (b : C(↥(H : Subgroup G), C(↥(H : Subgroup G), M))) :
    C(G, C(G, M)) :=
  ContinuousMap.curry ⟨fun xy =>
    b (openSubgroupRetraction H xy.1) (openSubgroupRetraction H xy.2) -
      z xy.1 (openSubgroupRetraction H xy.1) (openSubgroupRetraction H xy.2) +
      z xy.1 xy.2 (openSubgroupRetraction H xy.2), by fun_prop⟩

/-- The corrected extension has the original ambient cocycle as its boundary. -/
theorem openSubgroupPrimitiveExtension_boundary (H : OpenSubgroup G)
    [LocallyCompactSpace ↥(H : Subgroup G)]
    (z : C(G, C(G, C(G, M))))
    (hz : ∀ a b c d : G, z b c d - z a c d + z a b d - z a b c = 0)
    (b : C(↥(H : Subgroup G), C(↥(H : Subgroup G), M)))
    (hb : ∀ a b' c : ↥(H : Subgroup G),
      b b' c - b a c + b a b' = z a b' c)
    (g₀ g₁ g₂ : G) :
    openSubgroupPrimitiveExtension H z b g₁ g₂ -
        openSubgroupPrimitiveExtension H z b g₀ g₂ +
        openSubgroupPrimitiveExtension H z b g₀ g₁ = z g₀ g₁ g₂ := by
  let r := openSubgroupRetraction H
  have hA := hz g₀ (r g₀) (r g₁) (r g₂)
  have hB := hz g₀ g₁ (r g₁) (r g₂)
  have hC := hz g₀ g₁ g₂ (r g₂)
  change (b (r g₁) (r g₂) - z g₁ (r g₁) (r g₂) + z g₁ g₂ (r g₂)) -
      (b (r g₀) (r g₂) - z g₀ (r g₀) (r g₂) + z g₀ g₂ (r g₂)) +
      (b (r g₀) (r g₁) - z g₀ (r g₀) (r g₁) + z g₀ g₁ (r g₁)) =
    z g₀ g₁ g₂
  calc
    _ = z g₀ g₁ g₂ +
        (b (r g₁) (r g₂) - b (r g₀) (r g₂) + b (r g₀) (r g₁) -
          z (r g₀) (r g₁) (r g₂)) +
        (z (r g₀) (r g₁) (r g₂) - z g₀ (r g₁) (r g₂) +
          z g₀ (r g₀) (r g₂) - z g₀ (r g₀) (r g₁)) -
        (z g₁ (r g₁) (r g₂) - z g₀ (r g₁) (r g₂) +
          z g₀ g₁ (r g₂) - z g₀ g₁ (r g₁)) +
        (z g₁ g₂ (r g₂) - z g₀ g₂ (r g₂) +
          z g₀ g₁ (r g₂) - z g₀ g₁ g₂) := by abel
    _ = z g₀ g₁ g₂ := by rw [hb, sub_self, hA, hB, hC]; abel

/-- The corrected primitive remains equivariant under the open subgroup
for an arbitrary, possibly nontrivial, coefficient action. -/
theorem openSubgroupPrimitiveExtension_equivariant
    {R : Type*} [Ring R] [TopologicalSpace R] [Module R M]
    (ρ : ContRepresentation R G M)
    (H : OpenSubgroup G) [LocallyCompactSpace ↥(H : Subgroup G)]
    (z : C(G, C(G, C(G, M))))
    (hz : ∀ (h : ↥(H : Subgroup G)) (a b c : G),
      ρ (h : G) (z a b c) = z ((h : G) * a) ((h : G) * b) ((h : G) * c))
    (b : C(↥(H : Subgroup G), C(↥(H : Subgroup G), M)))
    (hb : ∀ h a c : ↥(H : Subgroup G), ρ (h : G) (b a c) = b (h * a) (h * c))
    (h : ↥(H : Subgroup G)) (g₀ g₁ : G) :
    ρ (h : G) (openSubgroupPrimitiveExtension H z b g₀ g₁) =
      openSubgroupPrimitiveExtension H z b ((h : G) * g₀) ((h : G) * g₁) := by
  change ρ (h : G)
      (b (openSubgroupRetraction H g₀) (openSubgroupRetraction H g₁) -
        z g₀ (openSubgroupRetraction H g₀) (openSubgroupRetraction H g₁) +
        z g₀ g₁ (openSubgroupRetraction H g₁)) =
    b (openSubgroupRetraction H ((h : G) * g₀))
        (openSubgroupRetraction H ((h : G) * g₁)) -
      z ((h : G) * g₀) (openSubgroupRetraction H ((h : G) * g₀))
        (openSubgroupRetraction H ((h : G) * g₁)) +
      z ((h : G) * g₀) ((h : G) * g₁)
        (openSubgroupRetraction H ((h : G) * g₁))
  rw [openSubgroupRetraction_subgroup_mul, openSubgroupRetraction_subgroup_mul,
    map_add, map_sub, hb, hz, hz]
  rfl

end ContinuousCohomology
