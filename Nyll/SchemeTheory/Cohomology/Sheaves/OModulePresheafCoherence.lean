/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Related adapted Anthropic FLT sources:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


module

public import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions

/-!
# Coherence of operations on module presheaves

Kernels, images, cokernels, products and finite powers preserve the appropriate coherence
properties. The unit presheaf and its pushforward along a closed immersion are coherent and
quasicoherent.
-/

public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

section KerImCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)

/-- Over a locally Noetherian scheme, the kernel of a map from a coherent presheaf is coherent. -/
theorem isCoherent_ker [IsLocallyNoetherian V] (hF : F.IsCoherent) : (ker φ).IsCoherent := fun U =>
  by
  have := hF U
  have : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  have : _root_.IsNoetherian Γ(V, U.1) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective ((kerImSES φ).inc.appSections U.1) ((kerImSES φ).injective U.1)

/-- The image of a map from a coherent presheaf is coherent. -/
theorem isCoherent_im (hF : F.IsCoherent) : (im φ).IsCoherent := fun U => by
  have := hF U
  exact Module.Finite.of_surjective ((kerImSES φ).proj.appSections U.1) ((kerImSES φ).surjective
    U.1)

/-- The cokernel of a map into a coherent presheaf is coherent. -/
theorem isCoherent_coker (hG : G.IsCoherent) : (coker φ).IsCoherent := fun U => by
  have := hG U
  exact Module.Finite.of_surjective ((imCokerSES φ).proj.appSections U.1) ((imCokerSES
    φ).surjective U.1)

/-- The cokernel of a map of quasicoherent presheaves is quasicoherent. -/
theorem isQuasicoherent_coker (hG : G.IsQuasicoherent) (hF : F.IsQuasicoherent) :
    (coker φ).IsQuasicoherent := fun U f => by
  refine ⟨fun x => x.inductionOn' fun x₀ => ?_, fun y => y.inductionOn' fun y₀ hy => ?_⟩
  · obtain ⟨n, y, hy⟩ := (hG U f).1 x₀
    exact ⟨n, Submodule.Quotient.mk y, congrArg Submodule.Quotient.mk hy⟩
  · obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    obtain ⟨n, w, hw⟩ := (hF U f).1 z
    have h1 : G.res (V.basicOpen_le f) ((f ^ n : Γ(V, U.1)) • y₀ - φ.app U.1 w) = 0 := by
      rw [map_sub, G.res_smul, ← hz, ← φ.app_smul, ← hw]
      exact sub_eq_zero.mpr (φ.naturality_apply (V.basicOpen_le f) w)
    obtain ⟨m, hm⟩ := (hG U f).2 _ h1
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
    exact ⟨m + n, (Submodule.Quotient.mk_eq_zero _).mpr
      ⟨(f ^ m : Γ(V, U.1)) • w, (φ.app_smul U.1 _ _).trans hm.symm⟩⟩

/-- The kernel of a map of quasicoherent presheaves is quasicoherent. -/
theorem isQuasicoherent_ker (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    (ker φ).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n, y', hy'⟩ := (hF U f).1 x.1
    have h1 : G.res (V.basicOpen_le f) (φ.app U.1 y') = 0 := by
      have hnat := φ.naturality_apply (V.basicOpen_le f) y'
      rw [hy', φ.app_smul, LinearMap.mem_ker.mp x.2, smul_zero] at hnat
      exact hnat.symm
    obtain ⟨m, hm⟩ := (hG U f).2 _ h1
    refine ⟨m + n, ⟨(f ^ m : Γ(V, U.1)) • y',
      LinearMap.mem_ker.mpr ((φ.app_smul U.1 _ _).trans hm)⟩, Subtype.ext ?_⟩
    change F.res (V.basicOpen_le f) ((f ^ m : Γ(V, U.1)) • y')
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ (m + n)) • x.1
    rw [F.res_smul, hy', smul_smul, ← map_mul, ← pow_add]
  · exact ((hF U f).2 y.1 (congrArg Subtype.val hy)).imp fun n hn => Subtype.ext hn

/-- The image of a map of quasicoherent presheaves is quasicoherent. -/
theorem isQuasicoherent_im (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    (im φ).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨s, hs⟩ := x.2
    obtain ⟨n, y', hy'⟩ := (hF U f).1 s
    refine ⟨n, ⟨φ.app U.1 y', y', rfl⟩, Subtype.ext ?_⟩
    change G.res (V.basicOpen_le f) (φ.app U.1 y')
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x.1
    rw [← φ.naturality_apply, hy', φ.app_smul, hs]
  · exact ((hG U f).2 y.1 (congrArg Subtype.val hy)).imp fun n hn => Subtype.ext hn

end KerImCoker

/-- Products of two coherent presheaves are coherent. -/
theorem isCoherent_prod {F G : OModulePresheaf π} (hF : F.IsCoherent) (hG : G.IsCoherent) :
    (F.prod G).IsCoherent :=
  fun U => by have := hF U; have := hG U; exact Module.Finite.prod

/-- Products of two quasicoherent presheaves are quasicoherent. -/
theorem isQuasicoherent_prod {F G : OModulePresheaf π} (hF : F.IsQuasicoherent) (hG :
  G.IsQuasicoherent) :
    (F.prod G).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n₁, y₁, hy₁⟩ := (hF U f).1 x.1; obtain ⟨n₂, y₂, hy₂⟩ := (hG U f).1 x.2
    exact ⟨n₁ + n₂, ((f ^ n₂ : Γ(V, U.1)) • y₁, (f ^ n₁ : Γ(V, U.1)) • y₂), Prod.ext
      (show F.res _ ((f ^ n₂ : Γ(V, U.1)) • y₁) = _ • x.1 by
        rw [F.res_smul, hy₁, smul_smul, ← map_mul, ← pow_add, Nat.add_comm])
      (show G.res _ ((f ^ n₁ : Γ(V, U.1)) • y₂) = _ • x.2 by
        rw [G.res_smul, hy₂, smul_smul, ← map_mul, ← pow_add])⟩
  · obtain ⟨n₁, hn₁⟩ := (hF U f).2 y.1 (congrArg Prod.fst hy)
    obtain ⟨n₂, hn₂⟩ := (hG U f).2 y.2 (congrArg Prod.snd hy)
    exact ⟨n₁ + n₂, Prod.ext
      (show (f ^ (n₁ + n₂) : Γ(V, U.1)) • y.1 = 0 by
        rw [Nat.add_comm, pow_add, mul_smul, hn₁, smul_zero])
      (show (f ^ (n₁ + n₂) : Γ(V, U.1)) • y.2 = 0 by
        rw [pow_add, mul_smul, hn₂, smul_zero])⟩

/-- Finite powers of a coherent presheaf are coherent. -/
theorem isCoherent_pow {F : OModulePresheaf π} (n : ℕ) (hF : F.IsCoherent) : (F.pow n).IsCoherent :=
  fun U => by have := hF U; exact Module.Finite.pi

/-- Finite powers of a quasicoherent presheaf are quasicoherent. -/
theorem isQuasicoherent_pow {F : OModulePresheaf π} (n : ℕ) (hF : F.IsQuasicoherent) :
    (F.pow n).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · choose m y' hy' using fun i => (hF U f).1 (x i)
    refine ⟨∑ i, m i, fun i => (f ^ ((∑ j, m j) - m i) : Γ(V, U.1)) • y' i, funext fun i => ?_⟩
    change F.res _ ((f ^ ((∑ j, m j) - m i) : Γ(V, U.1)) • y' i)
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ ∑ j, m j) • x i
    rw [F.res_smul, hy' i, smul_smul, ← map_mul, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))]
  · choose m hm using fun i => (hF U f).2 (y i) (congrFun hy i)
    refine ⟨∑ i, m i, funext fun i => show (f ^ ∑ j, m j : Γ(V, U.1)) • y i = 0 from ?_⟩
    rw [show (∑ j, m j) = ((∑ j, m j) - m i) + m i from (Nat.sub_add_cancel
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm,
      pow_add, mul_smul, hm i, smul_zero]

/-- Restriction to an open with affine intersections preserves quasicoherence. -/
theorem isQuasicoherent_restrOpen {F : OModulePresheaf π} (W₀ : V.Opens)
    (haff : ∀ U : V.affineOpens, IsAffineOpen (U.1 ⊓ W₀)) (hF : F.IsQuasicoherent) :
    (F.restrOpen W₀).IsQuasicoherent := fun U f => by
  have hbo : V.basicOpen ((V.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ W₀ ≤ U.1)).op).hom f)
      = V.basicOpen f ⊓ W₀ := by
    rw [Scheme.basicOpen_res, inf_right_comm, inf_eq_right.mpr (V.basicOpen_le f)]
  obtain ⟨hs, ha⟩ := hF ⟨U.1 ⊓ W₀, haff U⟩
    ((V.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ W₀ ≤ U.1)).op).hom f)
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · let x₀ : F.obj (V.basicOpen f ⊓ W₀) := x
    obtain ⟨n, y, hy⟩ := hs (F.res hbo.le x₀)
    refine ⟨n, y, show F.res (inf_le_inf_right W₀ (V.basicOpen_le f)) y
      = (V.presheaf.map (homOfLE (inf_le_left : V.basicOpen f ⊓ W₀ ≤ V.basicOpen f)).op).hom
          ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n)) • x₀ from ?_⟩
    have key := congrArg (F.res hbo.ge) hy
    rw [F.res_res, F.res_smul, F.res_res, F.res_refl_apply] at key
    refine key.trans (congrArg (· • x₀) ?_)
    simp only [map_pow, ← CommRingCat.comp_apply, ← V.presheaf.map_comp, ← op_comp, homOfLE_comp]
  · let y₀ : F.obj (U.1 ⊓ W₀) := y
    refine (ha y₀ ?_).imp fun n hn => ?_
    · exact (F.res_res hbo.le (inf_le_inf_right W₀ (V.basicOpen_le f)) y₀).symm.trans
        ((congrArg (F.res hbo.le) (show F.res _ y = 0 from hy)).trans (map_zero _))
    · change (V.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ W₀ ≤ U.1)).op).hom (f ^ n) • y₀ = 0
      rw [map_pow]; exact hn

/-- The unit presheaf is coherent. -/
theorem isCoherent_unit (π : V ⟶ Spec (.of R)) : (unit π).IsCoherent :=
  fun U => Module.Finite.self Γ(V, U.1)

/-- The unit presheaf is quasicoherent. -/
theorem isQuasicoherent_unit (π : V ⟶ Spec (.of R)) : (unit π).IsQuasicoherent := by
  intro U f
  have := U.2.isLocalization_basicOpen f
  refine ⟨fun x₀ => ?_, fun y hy => ?_⟩
  · let x : Γ(V, V.basicOpen f) := x₀
    obtain ⟨⟨y, _, n, rfl⟩, hxy⟩ :=
      IsLocalization.surj (S := Γ(V, V.basicOpen f)) (.powers f) x
    exact ⟨n, y, hxy.symm.trans (mul_comm x _)⟩
  · obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
      (IsLocalization.map_eq_zero_iff (S := Γ(V, V.basicOpen f)) (.powers f) y).mp hy
    exact ⟨n, hc⟩

section PushUnit

variable {Z : Scheme.{u}} (i : Z ⟶ V) [IsClosedImmersion i]

/-- The pushforward of the unit along a closed immersion is coherent. -/
theorem isCoherent_pushforwardUnit : (pushforwardUnit π i).IsCoherent := fun U => by
  change @Module.Finite Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) _ _
    (Module.compHom _ (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom)
  let : Algebra Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap _ _) fun x =>
    (i.app_surjective U.1 U.2 x).imp fun a ha =>
      show (i.appLE U.1 _ le_rfl).hom a = x by rw [Scheme.Hom.appLE_eq_app]; exact ha

/-- The pushforward of the unit along a closed immersion is quasicoherent. -/
theorem isQuasicoherent_pushforwardUnit : (pushforwardUnit π i).IsQuasicoherent := fun U f => by
  let S := unit (i ≫ π)
  set g : Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom f with hg_def
  have hbo : i ⁻¹ᵁ V.basicOpen f = Z.basicOpen g := Scheme.preimage_basicOpen i f
  obtain ⟨hs, ha⟩ := isQuasicoherent_unit (i ≫ π) ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ g
  have hpow : ∀ n (y : Γ(Z, i ⁻¹ᵁ U.1)),
      (f ^ n : Γ(V, U.1)) • (show (pushforwardUnit π i).obj U.1 from y) = g ^ n * y := fun n y => by
    change (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom (f ^ n) * y = _
    rw [map_pow, Scheme.Hom.appLE_eq_app]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · let x₀ : Γ(Z, i ⁻¹ᵁ V.basicOpen f) := x
    obtain ⟨n, y, hny⟩ := hs (S.res hbo.ge x₀)
    refine ⟨n, y, ?_⟩
    have key := congrArg (S.res hbo.le) hny
    have hback : S.res hbo.le (S.res hbo.ge x₀) = x₀ :=
      (S.res_res hbo.le hbo.ge x₀).trans (S.res_refl_apply _ x₀)
    erw [S.res_res, S.res_smul] at key
    erw [hback] at key
    change S.res ((Opens.map i.base).monotone (V.basicOpen_le f)) y
      = (i.appLE (V.basicOpen f) (i ⁻¹ᵁ V.basicOpen f) le_rfl).hom
          ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n)) * x₀
    refine key.trans ?_
    congr 1
    rw [← CommRingCat.comp_apply (f := V.presheaf.map _), Scheme.Hom.map_appLE,
      ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp, map_pow,
      map_pow]
    congr 1
  · refine (ha y ?_).imp fun n hn => (hpow n y).trans hn
    refine (S.res_res hbo.ge ((Opens.map i.base).monotone (V.basicOpen_le f)) y).symm.trans ?_
    exact (congrArg (S.res hbo.ge)
      (show S.res ((Opens.map i.base).monotone (V.basicOpen_le f)) y = 0 from hy)).trans
        (map_zero _)

end PushUnit

/-- The affine short exact sequence inserting a zero last coordinate into a finite power and
projecting to that coordinate. -/
noncomputable def AffSES.powSucc (F : OModulePresheaf π) (m : ℕ) :
    AffSES (F.pow m) (F.pow (m + 1)) F := by
  let ιapp : ∀ U : V.affineOpens, (F.pow m).obj U.1 →ₗ[R] (F.pow (m + 1)).obj U.1 :=
    fun U => LinearMap.pi fun k =>
      Fin.lastCases (0 : (Fin m → F.obj U.1) →ₗ[R] F.obj U.1) (fun j => LinearMap.proj j) k
  have hlast : ∀ (U : V.affineOpens) (g : (F.pow m).obj U.1), ιapp U g (Fin.last m) = 0 := by
    intro U g
    change (Fin.lastCases (0 : (Fin m → F.obj U.1) →ₗ[R] F.obj U.1)
      (fun j => LinearMap.proj j) (Fin.last m) : _ →ₗ[R] _) g = 0
    rw [Fin.lastCases_last]; rfl
  have hcast : ∀ (U : V.affineOpens) (g : (F.pow m).obj U.1) (j : Fin m),
      ιapp U g j.castSucc = (g : Fin m → F.obj U.1) j := by
    intro U g j
    change (Fin.lastCases (0 : (Fin m → F.obj U.1) →ₗ[R] F.obj U.1)
      (fun j => LinearMap.proj j) j.castSucc : _ →ₗ[R] _) g = g j
    rw [Fin.lastCases_castSucc]; rfl
  exact
    { inc :=
        { app := ιapp
          app_smul := fun U a g => funext fun k => by
            refine Fin.lastCases ?_ (fun j => ?_) k
            · rw [show (a • ιapp U g) (Fin.last m) = a • ιapp U g (Fin.last m) from rfl,
                hlast U (a • g), hlast U g, smul_zero]
            · rw [show (a • ιapp U g) j.castSucc = a • ιapp U g j.castSucc from rfl,
                hcast U (a • g) j, hcast U g j]; rfl
          naturality := fun {U U'} h => LinearMap.ext fun g => funext fun k => by
            refine Fin.lastCases ?_ (fun j => ?_) k
            · rw [LinearMap.comp_apply, LinearMap.comp_apply,
                show (F.pow (m + 1)).res h (ιapp U' g) (Fin.last m)
                  = F.res h (ιapp U' g (Fin.last m)) from rfl,
                hlast U, hlast U', map_zero]
            · rw [LinearMap.comp_apply, LinearMap.comp_apply,
                show (F.pow (m + 1)).res h (ιapp U' g) j.castSucc
                  = F.res h (ιapp U' g j.castSucc) from rfl,
                hcast U, hcast U']; rfl }
      proj :=
        { app := fun U => LinearMap.proj (R := R) (φ := fun _ : Fin (m + 1) => F.obj U.1)
            (Fin.last m)
          app_smul := fun U a x => rfl
          naturality := fun {U U'} h => rfl }
      injective := fun U g g' hgg' => funext fun j =>
        (hcast U g j).symm.trans ((congrFun hgg' j.castSucc).trans (hcast U g' j))
      surjective := fun U x => ⟨fun _ => x, rfl⟩
      exact := fun U => le_antisymm
        (LinearMap.range_le_ker_iff.mpr (LinearMap.ext fun g => hlast U g))
        (fun g hg => ⟨fun j => g j.castSucc, funext fun k => Fin.lastCases
          ((hlast U _).trans (LinearMap.mem_ker.mp hg).symm)
          (fun j => hcast U _ j) k⟩) }

end AlgebraicGeometry.OModulePresheaf
