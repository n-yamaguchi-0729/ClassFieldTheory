/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousCorestriction
public import Nyll.GaloisCohomology.Topology.ContinuousCrossedHom
public import Nyll.GaloisCohomology.Topology.ContinuousH0Naturality

/-!
# Continuous cup products in total degree two

The degree-one product is the homogeneous Alexander–Whitney product.
The boundary comparisons use the original equivariant cochains.
-/

@[expose] public section

open CategoryTheory TopRep ContRepresentation
open scoped Topology

noncomputable section

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : TopRep.{u} ℤ G}
variable (p : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (hp : Continuous (fun x : A × B => p x.1 x.2))
    (he : ∀ (g : G) (a : A) (b : B), p (A.ρ g a) (B.ρ g b) = C.ρ g (p a b))

private theorem cochainZero_equivariant {X : TopRep.{u} ℤ G}
    (f : (homogeneousCochains X).X 0) (g a : G) :
    X.ρ g (f.1 a) = f.1 (g * a) := by
  have h := congrArg (fun τ => τ (g * a)) (f.2 g)
  change X.ρ g (f.1 (g⁻¹ * (g * a))) = _ at h
  simpa only [inv_mul_cancel_left] using h

/-- Evaluating the original homogeneous one-cochain commutes with left translation. -/
theorem cochainOne_equivariant {X : TopRep.{u} ℤ G}
    (f : (homogeneousCochains X).X 1) (g a b : G) :
    X.ρ g (f.1 a b) = f.1 (g * a) (g * b) := by
  have h := congrArg (fun τ => τ (g * a) (g * b)) (f.2 g)
  change X.ρ g (f.1 (g⁻¹ * (g * a)) (g⁻¹ * (g * b))) = _ at h
  simpa only [inv_mul_cancel_left] using h

/-- A homogeneous one-cocycle is additive along a path of three vertices. -/
theorem oneCocycle_add {X : TopRep.{u} ℤ G} (x : cocycles X 1) (a b c : G) :
    ((homogeneousCochains X).iCycles 1 x).1 a c =
      ((homogeneousCochains X).iCycles 1 x).1 a b +
        ((homogeneousCochains X).iCycles 1 x).1 b c := by
  let f := (homogeneousCochains X).iCycles 1 x
  have h := ConcreteCategory.congr_hom ((homogeneousCochains X).iCycles_d 1 2) x
  have hd := congrArg (fun w => w a b c) (homogeneousCochains.d_apply X 1 f)
  have hvalue := congrArg (fun w : (homogeneousCochains X).X 2 => w.1 a b c) h
  change (((homogeneousCochains X).d 1 2).hom f).1 a b c = 0 at hvalue
  rw [hd] at hvalue
  change f.1 b c - (f.1 a c - f.1 a b) = 0 at hvalue
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hvalue).symm).trans (add_comm _ _)

private theorem zeroBoundary_apply {X : TopRep.{u} ℤ G}
    (f : (homogeneousCochains X).X 0) (a b : G) :
    ((homogeneousCochains X).d 0 1 f).1 a b = f.1 b - f.1 a :=
  congrArg (fun w => w a b) (homogeneousCochains.d_apply X 0 f)

/-- The actual differential of a homogeneous one-cochain at three vertices. -/
theorem oneBoundary_apply {X : TopRep.{u} ℤ G}
    (f : (homogeneousCochains X).X 1) (a b c : G) :
    ((homogeneousCochains X).d 1 2 f).1 a b c = f.1 b c - (f.1 a c - f.1 a b) :=
  congrArg (fun w => w a b c) (homogeneousCochains.d_apply X 1 f)

variable [LocallyCompactSpace G]

/-- The pointwise Alexander–Whitney product on three original vertices. -/
def cupOneOneTuple (x : (homogeneousCochains A).X 1)
    (y : (homogeneousCochains B).X 1) : C(Fin 3 → G, C) :=
  ⟨fun a => p (x.1 (a 0) (a 1)) (y.1 (a 1) (a 2)), by
    have hx : Continuous (fun a : Fin 3 → G => x.1 (a 0) (a 1)) :=
      (x.1.continuous.comp (continuous_apply 0)).eval (continuous_apply 1)
    have hy : Continuous (fun a : Fin 3 → G => y.1 (a 1) (a 2)) :=
      (y.1.continuous.comp (continuous_apply 1)).eval (continuous_apply 2)
    exact hp.comp (hx.prodMk hy)⟩

include he in
/-- The tuple product is equivariant for the original coefficient actions. -/
theorem cupOneOneTuple_equivariant
    (x : (homogeneousCochains A).X 1) (y : (homogeneousCochains B).X 1)
    (g : G) (a : Fin 3 → G) :
    cupOneOneTuple p hp x y (fun i => g * a i) = C.ρ g (cupOneOneTuple p hp x y a) := by
  change p (x.1 (g * a 0) (g * a 1)) (y.1 (g * a 1) (g * a 2)) =
    C.ρ g (p (x.1 (a 0) (a 1)) (y.1 (a 1) (a 2)))
  rw [← cochainOne_equivariant x, ← cochainOne_equivariant y, he]

/-- The actual homogeneous cochain cup in bidegree (1,1). -/
def cupOneOneCochain (x : (homogeneousCochains A).X 1)
    (y : (homogeneousCochains B).X 1) : (homogeneousCochains C).X 2 :=
  homogeneousCochainOfTuple G C 2 (cupOneOneTuple p hp x y)
    (cupOneOneTuple_equivariant p hp he x y)

theorem cupOneOneCochain_apply (x : (homogeneousCochains A).X 1)
    (y : (homogeneousCochains B).X 1) (a b c : G) :
    (cupOneOneCochain p hp he x y).1 a b c = p (x.1 a b) (y.1 b c) :=
  congrArg (fun w : C(Fin 3 → G, C) => w ![a, b, c])
    (homogeneousCochainOfTuple_apply G C 2 (cupOneOneTuple p hp x y)
      (cupOneOneTuple_equivariant p hp he x y))

/-- The original homogeneous product of two one-cocycles has vanishing differential. -/
theorem oneOne_mem_cycles (x : cocycles A 1) (y : cocycles B 1) :
    (homogeneousCochains C).d 2 3
      (cupOneOneCochain p hp he ((homogeneousCochains A).iCycles 1 x)
        ((homogeneousCochains B).iCycles 1 y)) = 0 := by
  let f := (homogeneousCochains A).iCycles 1 x
  let g := (homogeneousCochains B).iCycles 1 y
  let w := cupOneOneCochain p hp he f g
  apply Subtype.ext
  ext a b c d
  rw [congrArg (fun v => v a b c d) (homogeneousCochains.d_apply C 2 w)]
  change w.1 b c d - (w.1 a c d - (w.1 a b d - w.1 a b c)) = 0
  have hw (i j k : G) : w.val i j k = p (f.val i j) (g.val j k) :=
    cupOneOneCochain_apply p hp he f g i j k
  have hf : f.val a c = f.val a b + f.val b c := oneCocycle_add x a b c
  have hg : g.val b d = g.val b c + g.val c d := oneCocycle_add y b c d
  rw [hw b c d, hw a c d, hw a b d, hw a b c]
  simp only [hf, hg, map_add, LinearMap.add_apply]
  abel

/-- The homogeneous product of two actual cocycles. -/
def cupOneOneCocycle (x : cocycles A 1) (y : cocycles B 1) : cocycles C 2 := by
  let X := homogeneousCochains C
  let z := cupOneOneCochain p hp he ((homogeneousCochains A).iCycles 1 x)
    ((homogeneousCochains B).iCycles 1 y)
  let l := CrossedHom.scalarLine z
  have hz : l ≫ X.d 2 3 = 0 := by
    exact CrossedHom.scalarLine_comp_eq_zero z (X.d 2 3) (oneOne_mem_cycles p hp he x y)
  exact X.liftCycles l 3 (CochainComplex.next ℕ 2) hz (ULift.up (1 : ℤ))

theorem iCycles_cupOneOneCocycle (x : cocycles A 1) (y : cocycles B 1) :
    (homogeneousCochains C).iCycles 2 (cupOneOneCocycle p hp he x y) =
      cupOneOneCochain p hp he ((homogeneousCochains A).iCycles 1 x)
        ((homogeneousCochains B).iCycles 1 y) := by
  let X := homogeneousCochains C
  let z := cupOneOneCochain p hp he ((homogeneousCochains A).iCycles 1 x)
    ((homogeneousCochains B).iCycles 1 y)
  change X.iCycles 2 (X.liftCycles (CrossedHom.scalarLine z) 3
    (CochainComplex.next ℕ 2) _ (ULift.up (1 : ℤ))) = z
  rw [← ConcreteCategory.comp_apply, X.liftCycles_i]
  exact CrossedHom.scalarLine_one z

private theorem cupOneOneCocycle_apply (x : cocycles A 1) (y : cocycles B 1) (a b c : G) :
    ((homogeneousCochains C).iCycles 2 (cupOneOneCocycle p hp he x y)).val a b c =
      p (((homogeneousCochains A).iCycles 1 x).val a b)
        (((homogeneousCochains B).iCycles 1 y).val b c) :=
  (congrArg (fun f : (homogeneousCochains C).X 2 => f.val a b c)
    (iCycles_cupOneOneCocycle p hp he x y)).trans
      (cupOneOneCochain_apply p hp he _ _ a b c)

private theorem cupOneOneCocycle_add_left (x x' : cocycles A 1) (y : cocycles B 1) :
    cupOneOneCocycle p hp he (x + x') y =
      cupOneOneCocycle p hp he x y + cupOneOneCocycle p hp he x' y := by
  let X := homogeneousCochains A
  let Y := homogeneousCochains B
  apply (ModuleCat.mono_iff_injective ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map
    ((homogeneousCochains C).iCycles 2))).mp inferInstance
  change (homogeneousCochains C).iCycles 2 (cupOneOneCocycle p hp he (x + x') y) =
    (homogeneousCochains C).iCycles 2
      (cupOneOneCocycle p hp he x y + cupOneOneCocycle p hp he x' y)
  simp only [map_add, iCycles_cupOneOneCocycle]
  apply Subtype.ext
  ext a b c
  let f := X.iCycles 1 x
  let f' := X.iCycles 1 x'
  let g := Y.iCycles 1 y
  change p (f.val a b + f'.val a b) (g.val b c) =
    (cupOneOneCochain p hp he f g).val a b c + (cupOneOneCochain p hp he f' g).val a b c
  rw [map_add, LinearMap.add_apply, cupOneOneCochain_apply p hp he f g a b c,
    cupOneOneCochain_apply p hp he f' g a b c]

private theorem cupOneOneCocycle_add_right (x : cocycles A 1) (y y' : cocycles B 1) :
    cupOneOneCocycle p hp he x (y + y') =
      cupOneOneCocycle p hp he x y + cupOneOneCocycle p hp he x y' := by
  let X := homogeneousCochains A
  let Y := homogeneousCochains B
  apply (ModuleCat.mono_iff_injective ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map
    ((homogeneousCochains C).iCycles 2))).mp inferInstance
  change (homogeneousCochains C).iCycles 2 (cupOneOneCocycle p hp he x (y + y')) =
    (homogeneousCochains C).iCycles 2
      (cupOneOneCocycle p hp he x y + cupOneOneCocycle p hp he x y')
  simp only [map_add, iCycles_cupOneOneCocycle]
  apply Subtype.ext
  ext a b c
  let f := X.iCycles 1 x
  let g := Y.iCycles 1 y
  let g' := Y.iCycles 1 y'
  change p (f.val a b) (g.val b c + g'.val b c) =
    (cupOneOneCochain p hp he f g).val a b c + (cupOneOneCochain p hp he f g').val a b c
  rw [map_add, cupOneOneCochain_apply p hp he f g a b c,
    cupOneOneCochain_apply p hp he f g' a b c]

/-- A continuous equivariant function of two vertices gives a homogeneous one-cochain. -/
def mixedPrimitive (f : C(G × G, C))
    (hf : ∀ (g a b : G), f (g * a, g * b) = C.ρ g (f (a, b))) :
    (homogeneousCochains C).X 1 :=
  ⟨ContinuousMap.curry f, fun g => by
    ext a b
    change C.ρ g (f (g⁻¹ * a, g⁻¹ * b)) = f (a, b)
    rw [← hf, mul_inv_cancel_left, mul_inv_cancel_left]⟩

/-- The homogeneous Alexander–Whitney cochain product in bidegree `(0, 1)`. -/
def cupZeroOneCochain (x : (homogeneousCochains A).X 0) (y : (homogeneousCochains B).X 1) :
    (homogeneousCochains C).X 1 :=
  mixedPrimitive
    ⟨fun z => p (x.1 z.1) (y.1 z.1 z.2), by
      have hy : Continuous (fun z : G × G => y.1 z.1 z.2) :=
        (y.1.continuous.comp continuous_fst).eval continuous_snd
      exact hp.comp ((x.1.continuous.comp continuous_fst).prodMk hy)⟩
    (fun g a b => by
      change p (x.1 (g * a)) (y.1 (g * a) (g * b)) = C.ρ g (p (x.1 a) (y.1 a b))
      rw [← cochainZero_equivariant x, ← cochainOne_equivariant y, he])

/-- The homogeneous Alexander–Whitney cochain product in bidegree `(1, 0)`. -/
def cupOneZeroCochain (x : (homogeneousCochains A).X 1) (y : (homogeneousCochains B).X 0) :
    (homogeneousCochains C).X 1 :=
  mixedPrimitive
    ⟨fun z => p (x.1 z.1 z.2) (y.1 z.2), by
      have hx : Continuous (fun z : G × G => x.1 z.1 z.2) :=
        (x.1.continuous.comp continuous_fst).eval continuous_snd
      exact hp.comp (hx.prodMk (y.1.continuous.comp continuous_snd))⟩
    (fun g a b => by
      change p (x.1 (g * a) (g * b)) (y.1 (g * b)) = C.ρ g (p (x.1 a b) (y.1 b))
      rw [← cochainOne_equivariant x, ← cochainZero_equivariant y, he])

/-- The boundary of the mixed cup has the positive sign in bidegree `(0, 1)`. -/
theorem d_cupZeroOneCochain_apply
    (x : (homogeneousCochains A).X 0) (y : (homogeneousCochains B).X 1) (a b c : G) :
    ((homogeneousCochains C).d 1 2 (cupZeroOneCochain p hp he x y)).1 a b c =
      p (((homogeneousCochains A).d 0 1 x).1 a b) (y.1 b c) +
        p (x.1 a) (((homogeneousCochains B).d 1 2 y).1 a b c) := by
  rw [oneBoundary_apply, zeroBoundary_apply, oneBoundary_apply]
  change p (x.1 b) (y.1 b c) - (p (x.1 a) (y.1 a c) - p (x.1 a) (y.1 a b)) =
    p (x.1 b - x.1 a) (y.1 b c) + p (x.1 a) (y.1 b c - (y.1 a c - y.1 a b))
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- The boundary of the mixed cup has the negative sign in bidegree `(1, 0)`. -/
theorem d_cupOneZeroCochain_apply
    (x : (homogeneousCochains A).X 1) (y : (homogeneousCochains B).X 0) (a b c : G) :
    ((homogeneousCochains C).d 1 2 (cupOneZeroCochain p hp he x y)).1 a b c =
      p (((homogeneousCochains A).d 1 2 x).1 a b c) (y.1 c) -
        p (x.1 a b) (((homogeneousCochains B).d 0 1 y).1 b c) := by
  rw [oneBoundary_apply, oneBoundary_apply, zeroBoundary_apply]
  change p (x.1 b c) (y.1 c) - (p (x.1 a c) (y.1 c) - p (x.1 a b) (y.1 b)) =
    p (x.1 b c - (x.1 a c - x.1 a b)) (y.1 c) - p (x.1 a b) (y.1 c - y.1 b)
  simp only [map_sub, LinearMap.sub_apply]
  abel

omit [LocallyCompactSpace G] in
/-- A homogeneous degree-two boundary has zero class in continuous cohomology. -/
theorem class_zero_of_degreeTwo_boundary (z : cocycles C 2)
    (b : (homogeneousCochains C).X 1)
    (h : (homogeneousCochains C).d 1 2 b = (homogeneousCochains C).iCycles 2 z) :
    π C 2 z = 0 := by
  let D := homogeneousCochains C
  have hb : D.toCycles 1 2 b = z := by
    apply (ModuleCat.mono_iff_injective
      ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map (D.iCycles 2))).mp inferInstance
    exact (ConcreteCategory.congr_hom (D.toCycles_i 1 2) b).trans h
  change D.homologyπ 2 z = 0
  rw [← hb]
  exact ConcreteCategory.congr_hom (D.toCycles_comp_homologyπ 1 2) b

omit [LocallyCompactSpace G] in
private theorem oneCocycle_boundary_apply {X : TopRep.{u} ℤ G}
    (z : cocycles X 1) (a b c : G) :
    ((homogeneousCochains X).d 1 2 ((homogeneousCochains X).iCycles 1 z)).val a b c = 0 := by
  let D := homogeneousCochains X
  have h := congrArg (fun f => TopModuleCat.Hom.hom f z) (D.iCycles_d 1 2)
  have hz : (D.d 1 2).hom ((D.iCycles 1).hom z) = 0 := by
    simpa only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
      TopModuleCat.hom_zero, _root_.zero_apply] using h
  exact congrArg (fun f : D.X 2 => f.val a b c) hz

private theorem cupOneOne_boundary_left (x : cocycles A 1) (y : cocycles B 1)
    (hx : π A 1 x = 0) : π C 2 (cupOneOneCocycle p hp he x y) = 0 := by
  obtain ⟨s, hs⟩ := exists_boundary_of_π_eq_zero A 0 x hx
  let X := homogeneousCochains A
  let Y := homogeneousCochains B
  let D := homogeneousCochains C
  let f := X.iCycles 1 x
  let g := Y.iCycles 1 y
  let z := cupOneOneCocycle p hp he x y
  let t := cupZeroOneCochain p hp he s g
  refine class_zero_of_degreeTwo_boundary z t ?_
  apply Subtype.ext
  ext a b c
  have hg : (Y.d 1 2 g).val a b c = 0 := oneCocycle_boundary_apply y a b c
  have hs' : (X.d 0 1 s).val a b = f.val a b :=
    congrArg (fun w : X.X 1 => w.val a b) hs
  change (D.d 1 2 t).val a b c = (D.iCycles 2 z).val a b c
  calc
    _ = p ((X.d 0 1 s).val a b) (g.val b c) + p (s.val a) ((Y.d 1 2 g).val a b c) :=
      d_cupZeroOneCochain_apply p hp he s g a b c
    _ = p (f.val a b) (g.val b c) := by rw [hs', hg, map_zero, add_zero]
    _ = _ := (cupOneOneCocycle_apply p hp he x y a b c).symm

private theorem cupOneOne_boundary_right (x : cocycles A 1) (y : cocycles B 1)
    (hy : π B 1 y = 0) : π C 2 (cupOneOneCocycle p hp he x y) = 0 := by
  obtain ⟨s, hs⟩ := exists_boundary_of_π_eq_zero B 0 y hy
  let X := homogeneousCochains A
  let Y := homogeneousCochains B
  let D := homogeneousCochains C
  let f := X.iCycles 1 x
  let g := Y.iCycles 1 y
  let z := cupOneOneCocycle p hp he x y
  let t := cupOneZeroCochain p hp he f s
  refine class_zero_of_degreeTwo_boundary z (-t) ?_
  apply Subtype.ext
  ext a b c
  have hf : (X.d 1 2 f).val a b c = 0 := oneCocycle_boundary_apply x a b c
  have hs' : (Y.d 0 1 s).val b c = g.val b c :=
    congrArg (fun w : Y.X 1 => w.val b c) hs
  have hneg : (D.d 1 2 (-t)).val a b c = -(D.d 1 2 t).val a b c :=
    congrArg (fun w : D.X 2 => w.val a b c) (map_neg (D.d 1 2).hom t)
  have ht : (D.d 1 2 t).val a b c = -p (f.val a b) (g.val b c) := by
    calc
      _ = p ((X.d 1 2 f).val a b c) (s.val c) - p (f.val a b) ((Y.d 0 1 s).val b c) :=
        d_cupOneZeroCochain_apply p hp he f s a b c
      _ = _ := by rw [hf, hs', map_zero, LinearMap.zero_apply, zero_sub]
  change (D.d 1 2 (-t)).val a b c = (D.iCycles 2 z).val a b c
  rw [hneg, ht, neg_neg]
  exact (cupOneOneCocycle_apply p hp he x y a b c).symm

private theorem cupOneOne_class_congr (x x' : cocycles A 1) (y y' : cocycles B 1)
    (hx : π A 1 x = π A 1 x') (hy : π B 1 y = π B 1 y') :
    π C 2 (cupOneOneCocycle p hp he x y) =
      π C 2 (cupOneOneCocycle p hp he x' y') := by
  have h₁ := cupOneOne_boundary_left p hp he (x - x') y
    (by rw [map_sub, hx, sub_self])
  have h₂ := cupOneOne_boundary_right p hp he x' (y - y')
    (by rw [map_sub, hy, sub_self])
  have hleft := cupOneOneCocycle_add_left p hp he (x - x') x' y
  have hright := cupOneOneCocycle_add_right p hp he x' (y - y') y'
  rw [sub_add_cancel] at hleft hright
  rw [hleft, map_add, h₁, zero_add, hright, map_add, h₂, zero_add]

/-- The original continuous cup product on classes of degree one. -/
def cupOneOne (a : continuousCohomology 1 A) (b : continuousCohomology 1 B) :
    continuousCohomology 2 C :=
  π C 2 (cupOneOneCocycle p hp he ((π_surjective A 1 a).choose) ((π_surjective B 1 b).choose))

@[simp] theorem cupOneOne_π (x : cocycles A 1) (y : cocycles B 1) :
    cupOneOne p hp he (π A 1 x) (π B 1 y) = π C 2 (cupOneOneCocycle p hp he x y) :=
  cupOneOne_class_congr p hp he _ _ _ _
    (π_surjective A 1 (π A 1 x)).choose_spec (π_surjective B 1 (π B 1 y)).choose_spec

theorem cupOneOne_add_left (a a' : continuousCohomology 1 A) (b : continuousCohomology 1 B) :
    cupOneOne p hp he (a + a') b = cupOneOne p hp he a b + cupOneOne p hp he a' b := by
  obtain ⟨x, rfl⟩ := π_surjective A 1 a
  obtain ⟨x', rfl⟩ := π_surjective A 1 a'
  obtain ⟨y, rfl⟩ := π_surjective B 1 b
  rw [← map_add, cupOneOne_π, cupOneOne_π, cupOneOne_π, cupOneOneCocycle_add_left, map_add]

theorem cupOneOne_zero_left (b : continuousCohomology 1 B) : cupOneOne p hp he 0 b = 0 := by
  have h := cupOneOne_add_left p hp he 0 0 b
  rw [zero_add] at h
  exact add_eq_left.mp h.symm

theorem cupOneOne_neg_left (a : continuousCohomology 1 A) (b : continuousCohomology 1 B) :
    cupOneOne p hp he (-a) b = -cupOneOne p hp he a b := by
  have h := cupOneOne_add_left p hp he (-a) a b
  rw [neg_add_cancel, cupOneOne_zero_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem cupOneOne_add_right (a : continuousCohomology 1 A) (b b' : continuousCohomology 1 B) :
    cupOneOne p hp he a (b + b') = cupOneOne p hp he a b + cupOneOne p hp he a b' := by
  obtain ⟨x, rfl⟩ := π_surjective A 1 a
  obtain ⟨y, rfl⟩ := π_surjective B 1 b
  obtain ⟨y', rfl⟩ := π_surjective B 1 b'
  rw [← map_add, cupOneOne_π, cupOneOne_π, cupOneOne_π, cupOneOneCocycle_add_right, map_add]

/-- Substituting an invariant left coefficient gives a map of the original representations. -/
def cupLeftInvariant (a : A.invariants) : B ⟶ C := by
  let m : B →+ C := (p a.val).toAddMonoidHom
  let : Module ℤ B := B.hV2
  let : Module ℤ C := C.hV2
  refine TopRep.ofHom { toLinearMap := ?_, cont := ?_, isIntertwining' := ?_ }
  · exact
      { toFun := m
        map_add' := m.map_add
        map_smul' := fun z b => (congrArg m (int_smul_eq_zsmul B.hV2 z b)).trans
          ((map_zsmul m z b).trans (int_smul_eq_zsmul C.hV2 z (m b)).symm) }
  · change Continuous (fun b : B => p a.val b)
    have ha : Continuous (fun _ : B => a.val) := continuous_const
    exact hp.comp (ha.prodMk continuous_id)
  · intro g
    apply ContinuousLinearMap.ext
    intro b
    change p a.val (B.ρ g b) = C.ρ g (p a.val b)
    exact (congrArg (fun x => p x (B.ρ g b)) (a.property g)).symm.trans (he g a.val b)

/-- Bidegree (0,2) cup is the original coefficient map of the invariant
left argument, applied to degree-two cohomology. -/
def cupZeroTwo (a : continuousCohomology 0 A) (b : continuousCohomology 2 B) :
    continuousCohomology 2 C :=
  map (ContinuousMonoidHom.id G) (cupLeftInvariant p hp he ((zeroIso A).hom a)) 2 b

/-- Bidegree (2,0) cup is the original coefficient map of the invariant
right argument, applied to degree-two cohomology. -/
def cupTwoZero (a : continuousCohomology 2 A) (b : continuousCohomology 0 B) :
    continuousCohomology 2 C :=
  degreeTwoInvariantMap p hp he ((zeroIso B).hom b) a

omit [LocallyCompactSpace G] in
/-- Swapping the invariant argument and the pairing preserves the degree-two class. -/
theorem cupZeroTwo_flip (a : continuousCohomology 0 A) (b : continuousCohomology 2 B) :
    cupZeroTwo p hp he a b =
      cupTwoZero p.flip (hp.comp continuous_swap) (fun g b a => he g a b) b a := by
  let a₀ := (zeroIso A).hom a
  have h : cupLeftInvariant p hp he a₀ =
      rightInvariantCoefficientMap p.flip (hp.comp continuous_swap) (fun g b a => he g a b) a₀ := by
    let : Module ℤ B := B.hV2
    let : Module ℤ C := C.hV2
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := B.ρ) (π₂ := C.ρ)
    apply ContinuousLinearMap.ext
    intro b
    rfl
  change map (ContinuousMonoidHom.id G) (cupLeftInvariant p hp he a₀) 2 b =
    map (ContinuousMonoidHom.id G)
      (rightInvariantCoefficientMap p.flip (hp.comp continuous_swap) (fun g b a => he g a b) a₀) 2 b
  exact congrArg (fun f : B ⟶ C => map (ContinuousMonoidHom.id G) (X := B) f 2 b) h

theorem cupZeroTwo_add_left (a a' : continuousCohomology 0 A) (b : continuousCohomology 2 B) :
    cupZeroTwo p hp he (a + a') b = cupZeroTwo p hp he a b + cupZeroTwo p hp he a' b := by
  let e := (zeroIso A).hom
  have hpair (x y : A) (v : B) : p (x + y) v = p x v + p y v :=
    congrArg (fun f : B →ₗ[ℤ] C => f v) (map_add p x y)
  have h : cupLeftInvariant p hp he (e (a + a')) =
      cupLeftInvariant p hp he (e a) + cupLeftInvariant p hp he (e a') := by
    let : Module ℤ B := B.hV2
    let : Module ℤ C := C.hV2
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := B.ρ) (π₂ := C.ρ)
    apply ContinuousLinearMap.ext
    intro v
    change p (e (a + a')).val v = p (e a).val v + p (e a').val v
    rw [map_add]
    change p ((e a).val + (e a').val) v = _
    exact hpair _ _ _
  exact (congrArg (fun f : B ⟶ C => map (ContinuousMonoidHom.id G) (X := B) f 2 b) h).trans
    (continuousCohomology_map_add_apply
      (cupLeftInvariant p hp he (e a)) (cupLeftInvariant p hp he (e a')) 2 b)

omit [LocallyCompactSpace G] in
theorem cupZeroTwo_add_right (a : continuousCohomology 0 A) (b b' : continuousCohomology 2 B) :
    cupZeroTwo p hp he a (b + b') = cupZeroTwo p hp he a b + cupZeroTwo p hp he a b' :=
  map_add (map (ContinuousMonoidHom.id G) (X := B)
    (cupLeftInvariant p hp he ((zeroIso A).hom a)) 2).hom b b'

omit [LocallyCompactSpace G] in
theorem cupTwoZero_add_left (a a' : continuousCohomology 2 A) (b : continuousCohomology 0 B) :
    cupTwoZero p hp he (a + a') b = cupTwoZero p hp he a b + cupTwoZero p hp he a' b :=
  map_add (degreeTwoInvariantMap p hp he ((zeroIso B).hom b)) a a'

theorem cupTwoZero_add_right (a : continuousCohomology 2 A) (b b' : continuousCohomology 0 B) :
    cupTwoZero p hp he a (b + b') = cupTwoZero p hp he a b + cupTwoZero p hp he a b' := by
  let e := (zeroIso B).hom
  have h : rightInvariantCoefficientMap p hp he (e (b + b')) =
      rightInvariantCoefficientMap p hp he (e b) + rightInvariantCoefficientMap p hp he (e b') := by
    let : Module ℤ A := A.hV2
    let : Module ℤ C := C.hV2
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := A.ρ) (π₂ := C.ρ)
    apply ContinuousLinearMap.ext
    intro v
    change p v (e (b + b')).val = p v (e b).val + p v (e b').val
    rw [map_add]
    change p v ((e b).val + (e b').val) = _
    rw [map_add]
  exact (congrArg (fun f : A ⟶ C => map (ContinuousMonoidHom.id G) (X := A) f 2 a) h).trans
    (continuousCohomology_map_add_apply
      (rightInvariantCoefficientMap p hp he (e b))
      (rightInvariantCoefficientMap p hp he (e b')) 2 a)

omit [LocallyCompactSpace G] in
theorem cupZeroTwo_π (a : continuousCohomology 0 A) (z : cocycles B 2) :
    cupZeroTwo p hp he a (π B 2 z) =
      π C 2 (cocyclesMap (ContinuousMonoidHom.id G)
        (cupLeftInvariant p hp he ((zeroIso A).hom a)) 2 z) :=
  ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.id G)
    (cupLeftInvariant p hp he ((zeroIso A).hom a)) 2) z

omit [LocallyCompactSpace G] in
theorem cupTwoZero_π (z : cocycles A 2) (b : continuousCohomology 0 B) :
    cupTwoZero p hp he (π A 2 z) b =
      π C 2 (cocyclesMap (ContinuousMonoidHom.id G)
        (rightInvariantCoefficientMap p hp he ((zeroIso B).hom b)) 2 z) :=
  ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.id G)
    (rightInvariantCoefficientMap p hp he ((zeroIso B).hom b)) 2) z

omit [LocallyCompactSpace G] in
/-- The cocycle representing the invariant-left cup has the pointwise
Alexander–Whitney evaluation on the original representative. -/
theorem exists_cupZeroTwo_cocycle (x : cocycles A 0) (y : cocycles B 2) :
    ∃ z : cocycles C 2, π C 2 z = cupZeroTwo p hp he (π A 0 x) (π B 2 y) ∧
      ∀ a b c : G, ((homogeneousCochains C).iCycles 2 z).1 a b c =
        p (((homogeneousCochains A).iCycles 0 x).1 a)
          (((homogeneousCochains B).iCycles 2 y).1 a b c) := by
  let f := cupLeftInvariant p hp he ((zeroIso A).hom (π A 0 x))
  refine ⟨cocyclesMap (ContinuousMonoidHom.id G) f 2 y, (cupZeroTwo_π p hp he (π A 0 x) y).symm, ?_⟩
  intro a b c
  have h := congrArg (fun w : (homogeneousCochains C).X 2 => w.1 a b c) (ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) f) 2) y)
  change _ = p (((zeroIso A).hom (π A 0 x)).val)
    (((homogeneousCochains B).iCycles 2 y).1 a b c) at h
  rw [zeroIso_hom_π_apply A x a] at h
  exact h

omit [LocallyCompactSpace G] in
/-- The cocycle representing the invariant-right cup evaluates the degree-zero
argument at the last vertex of the original representative. -/
theorem exists_cupTwoZero_cocycle (x : cocycles A 2) (y : cocycles B 0) :
    ∃ z : cocycles C 2, π C 2 z = cupTwoZero p hp he (π A 2 x) (π B 0 y) ∧
      ∀ a b c : G, ((homogeneousCochains C).iCycles 2 z).1 a b c =
        p (((homogeneousCochains A).iCycles 2 x).1 a b c)
          (((homogeneousCochains B).iCycles 0 y).1 c) := by
  let f := rightInvariantCoefficientMap p hp he ((zeroIso B).hom (π B 0 y))
  refine ⟨cocyclesMap (ContinuousMonoidHom.id G) f 2 x, (cupTwoZero_π p hp he x (π B 0 y)).symm, ?_⟩
  intro a b c
  have h := congrArg (fun w : (homogeneousCochains C).X 2 => w.1 a b c) (ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) f) 2) x)
  change _ = p (((homogeneousCochains A).iCycles 2 x).1 a b c)
    (((zeroIso B).hom (π B 0 y)).val) at h
  rw [zeroIso_hom_π_apply B y c] at h
  exact h

section GroupMap

variable {J : Type u} [Group J] [TopologicalSpace J] [IsTopologicalGroup J] [LocallyCompactSpace J]
variable {A' B' C' : TopRep.{u} ℤ J}
variable (r : J →ₜ* G)
    (f : TopRep.res r.toMonoidHom A ⟶ A') (g : TopRep.res r.toMonoidHom B ⟶ B')
    (k : TopRep.res r.toMonoidHom C ⟶ C')
    (q : A' →ₗ[ℤ] B' →ₗ[ℤ] C') (hq : Continuous (fun t : A' × B' => q t.1 t.2))
    (hqe : ∀ (γ : J) (a : A') (b : B'), q (A'.ρ γ a) (B'.ρ γ b) = C'.ρ γ (q a b))

omit [LocallyCompactSpace G] [LocallyCompactSpace J] in
private theorem map_mappedCocycle_π {X : TopRep.{u} ℤ G} {X' : TopRep.{u} ℤ J}
    (φ : TopRep.res r.toMonoidHom X ⟶ X') (i : ℕ) (z : cocycles X i) :
    map r φ i (π X i z) = π X' i (cocyclesMap r φ i z) :=
  ConcreteCategory.congr_hom (π_map r φ i) z

private theorem mappedZeroCocycle_apply {X : TopRep.{u} ℤ G} {X' : TopRep.{u} ℤ J}
    (φ : TopRep.res r.toMonoidHom X ⟶ X') (z : cocycles X 0) (a : J) :
    ((homogeneousCochains X').iCycles 0 (cocyclesMap r φ 0 z)).val a =
      φ (((homogeneousCochains X).iCycles 0 z).val (r a)) := by
  change resolutionTupleHomeomorph J X' 1
    ((homogeneousCochains X').iCycles 0 (cocyclesMap r φ 0 z)).val (fun _ => a) = _
  rw [cochainOfMappedCocycle, resolutionTupleHomeomorph_cochainsMap]
  rfl

private theorem mappedOneCocycle_apply {X : TopRep.{u} ℤ G} {X' : TopRep.{u} ℤ J}
    (φ : TopRep.res r.toMonoidHom X ⟶ X') (z : cocycles X 1) (a b : J) :
    ((homogeneousCochains X').iCycles 1 (cocyclesMap r φ 1 z)).val a b =
      φ (((homogeneousCochains X).iCycles 1 z).val (r a) (r b)) := by
  change resolutionTupleHomeomorph J X' 2
    ((homogeneousCochains X').iCycles 1 (cocyclesMap r φ 1 z)).val ![a, b] = _
  rw [cochainOfMappedCocycle, resolutionTupleHomeomorph_cochainsMap]
  rfl

/-- The continuous cup of two degree-one classes is natural under compatible
coefficient maps along a continuous group homomorphism. -/
theorem map_cupOneOne (h : ∀ a b, k (p a b) = q (f a) (g b))
    (a : continuousCohomology 1 A) (b : continuousCohomology 1 B) :
    map r k 2 (cupOneOne p hp he a b) = cupOneOne q hq hqe (map r f 1 a) (map r g 1 b) := by
  obtain ⟨x, rfl⟩ := π_surjective A 1 a
  obtain ⟨y, rfl⟩ := π_surjective B 1 b
  rw [cupOneOne_π, map_mappedCocycle_π r k, map_mappedCocycle_π r f, map_mappedCocycle_π r g,
    cupOneOne_π]
  apply congrArg (π C' 2)
  apply (ModuleCat.mono_iff_injective ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map
    ((homogeneousCochains C').iCycles 2))).mp inferInstance
  apply Subtype.ext
  ext α β γ
  change ((homogeneousCochains C').iCycles 2
      (cocyclesMap r k 2 (cupOneOneCocycle p hp he x y))).val α β γ =
    ((homogeneousCochains C').iCycles 2 (cupOneOneCocycle q hq hqe
      (cocyclesMap r f 1 x) (cocyclesMap r g 1 y))).val α β γ
  rw [mappedRelativeCocycle_apply, iCycles_cupOneOneCocycle, iCycles_cupOneOneCocycle,
    cupOneOneCochain_apply, cupOneOneCochain_apply, mappedOneCocycle_apply, mappedOneCocycle_apply]
  exact h _ _

/-- The degree-two cup with an invariant right coefficient is natural
under the same coefficient maps. -/
theorem map_cupTwoZero (h : ∀ a b, k (p a b) = q (f a) (g b))
    (a : continuousCohomology 2 A) (b : continuousCohomology 0 B) :
    map r k 2 (cupTwoZero p hp he a b) = cupTwoZero q hq hqe (map r f 2 a) (map r g 0 b) := by
  obtain ⟨x, rfl⟩ := π_surjective A 2 a
  obtain ⟨y, rfl⟩ := π_surjective B 0 b
  let x' := cocyclesMap r f 2 x
  let y' := cocyclesMap r g 0 y
  obtain ⟨z, hz, hzval⟩ := exists_cupTwoZero_cocycle p hp he x y
  obtain ⟨z', hz', hz'val⟩ := exists_cupTwoZero_cocycle q hq hqe x' y'
  rw [← hz, map_mappedCocycle_π r k, map_mappedCocycle_π r f, map_mappedCocycle_π r g]
  change π C' 2 (cocyclesMap r k 2 z) = cupTwoZero q hq hqe (π A' 2 x') (π B' 0 y')
  rw [← hz']
  apply congrArg (π C' 2)
  apply (ModuleCat.mono_iff_injective ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map
    ((homogeneousCochains C').iCycles 2))).mp inferInstance
  apply Subtype.ext
  ext α β γ
  change ((homogeneousCochains C').iCycles 2 (cocyclesMap r k 2 z)).val α β γ =
    ((homogeneousCochains C').iCycles 2 z').val α β γ
  rw [mappedRelativeCocycle_apply, hzval, hz'val]
  change k _ = q (((homogeneousCochains A').iCycles 2 (cocyclesMap r f 2 x)).val α β γ)
    (((homogeneousCochains B').iCycles 0 (cocyclesMap r g 0 y)).val γ)
  rw [mappedRelativeCocycle_apply, mappedZeroCocycle_apply]
  exact h _ _

/-- The degree-two cup with an invariant left coefficient is natural
under the same coefficient maps. -/
theorem map_cupZeroTwo (h : ∀ a b, k (p a b) = q (f a) (g b))
    (a : continuousCohomology 0 A) (b : continuousCohomology 2 B) :
    map r k 2 (cupZeroTwo p hp he a b) = cupZeroTwo q hq hqe (map r f 0 a) (map r g 2 b) := by
  rw [cupZeroTwo_flip (A := A) (B := B) (C := C), cupZeroTwo_flip (A := A') (B := B') (C := C')]
  exact map_cupTwoZero p.flip (hp.comp continuous_swap) (fun γ b a => he γ a b) r g f k
    q.flip (hq.comp continuous_swap) (fun γ b a => hqe γ a b) (fun b a => h a b) b a

end GroupMap

end ContinuousCohomology
