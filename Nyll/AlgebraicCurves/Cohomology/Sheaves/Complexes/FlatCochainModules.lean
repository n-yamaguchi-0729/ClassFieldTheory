/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Geometry.Schemes.Cohomology.TwoAffineCoverFlatSections
import Nyll.AlgebraicCurves.Geometry.Projective.ModulesProjectiveSections

/-!
# OModule Presheaf flat cochain of Modules of locally Trivial
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.FlatCochains

universe u

section cechflat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem _root_.AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [Flat π] [IsSeparated π] (M
      : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (K : V.OrderedAffineCover) (i : ℕ) :
    Module.Flat R ((OModulePresheaf.ofModules π M).cochain K i) := by
  classical
  have : ∀ s : K.Idx i, Module.Flat R ((OModulePresheaf.ofModules π M).obj (K.inter s)) := fun s
    => by
    have haff : IsAffineOpen (K.inter s) := K.isAffineOpen_inter π s
    let := Scheme.TwoAffineOpenCover.algebraOfHom π (K.inter s)
    have : Module.Flat R Γ(V, K.inter s) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π _ haff
    have : Module.Projective Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Scheme.Modules.projective_sections_of_locallyTrivial M htriv ⟨K.inter s, haff⟩
    have : Module.Flat Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Module.Flat.of_projective
    exact Module.Flat.trans R Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s))
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R (K.Idx i) fun s => (OModulePresheaf.ofModules π M).obj
      (K.inter s)).symm

end cechflat
end AlgebraicCurves.Cohomology.Sheaves.Proofs.FlatCochains
end ProofImplementation
