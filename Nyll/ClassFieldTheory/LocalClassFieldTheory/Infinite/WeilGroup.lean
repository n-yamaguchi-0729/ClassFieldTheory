/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum
public import Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import Mathlib.Topology.Instances.Int

/-!
# The local Weil group

The Weil topology is the pullback topology using the discrete integers and
the actual arithmetic residue-degree map on the separable absolute Galois group.
-/

@[expose] public section

open scoped ValuativeRel commutatorElement

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory ProCGroups.Abelian

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical integer inclusion, written multiplicatively to match residue degree. -/
def localWeilIntegerInclusion : Multiplicative ℤ →* ZHatMul :=
  (Int.castRingHom ZHat).toAddMonoidHom.toMultiplicative

/-- Arithmetic integers are detected by their reductions in the profinite integers. -/
theorem localWeilIntegerInclusion_injective :
    Function.Injective localWeilIntegerInclusion := by
  intro a b hab
  exact Multiplicative.toAdd.injective
    (zHat_intCast_injective (congrArg Multiplicative.toAdd hab))

/-- The pullback with the actual residue degree and the canonical inclusion of the integers. -/
noncomputable def localWeilGroup :
    Subgroup (Gal(SeparableClosure K / K) × Multiplicative ℤ) :=
  ((localResidueDegree K).toMonoidHom.comp (MonoidHom.fst _ _)).eqLocus
    (localWeilIntegerInclusion.comp (MonoidHom.snd _ _))

/-- The continuous comparison with the absolute Galois group. -/
noncomputable def localWeilToAbsolute :
    localWeilGroup K →ₜ* Gal(SeparableClosure K / K) where
  toMonoidHom := (MonoidHom.fst _ _).comp (localWeilGroup K).subtype
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The same inclusion into the usual absolute Galois group. -/
noncomputable def localWeilToStandardAbsolute :
    localWeilGroup K →ₜ* Field.absoluteGaloisGroup K :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K).symm).comp
    (localWeilToAbsolute K)

/-- The continuous, integer-valued arithmetic degree of a Weil element. -/
noncomputable def localWeilDegree : localWeilGroup K →ₜ* Multiplicative ℤ where
  toMonoidHom := (MonoidHom.snd _ _).comp (localWeilGroup K).subtype
  continuous_toFun := continuous_snd.comp continuous_subtype_val

theorem localResidueDegree_localWeilToAbsolute (x : localWeilGroup K) :
    localResidueDegree K (localWeilToAbsolute K x) =
      localWeilIntegerInclusion (localWeilDegree K x) :=
  x.2

theorem localWeilToAbsolute_injective : Function.Injective (localWeilToAbsolute K) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · apply localWeilIntegerInclusion_injective
    calc
      localWeilIntegerInclusion (localWeilDegree K x) =
          localResidueDegree K (localWeilToAbsolute K x) :=
        (localResidueDegree_localWeilToAbsolute K x).symm
      _ = localResidueDegree K (localWeilToAbsolute K y) :=
        congrArg (localResidueDegree K) hxy
      _ = localWeilIntegerInclusion (localWeilDegree K y) :=
        localResidueDegree_localWeilToAbsolute K y

theorem localWeilDegree_surjective : Function.Surjective (localWeilDegree K) := by
  intro n
  obtain ⟨g, hg⟩ := localResidueDegree_surjective K (localWeilIntegerInclusion n)
  exact ⟨⟨(g, n), hg⟩, rfl⟩

theorem localWeilToAbsolute_denseRange : DenseRange (localWeilToAbsolute K) := by
  let : T2Space ZHatMul := by
    change T2Space ZHat
    infer_instance
  have hopen : IsOpenMap (localResidueDegree K) :=
    ProCGroups.ContinuousMonoidHom.isOpenMap_of_surjective_compact_t2
      (localResidueDegree K) (localResidueDegree_surjective K)
  have hdense : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ZHat)) := by
    exact (show Function.Surjective (Multiplicative.ofAdd : ZHat → ZHatMul) from
      fun z => ⟨z.toAdd, rfl⟩).denseRange.comp denseRange_intCast_zHat continuous_ofAdd
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨g, hg⟩
  have hnonempty : ((localResidueDegree K) '' U).Nonempty :=
    ⟨localResidueDegree K g, g, hg, rfl⟩
  obtain ⟨_, ⟨g', hg', hdeg⟩, ⟨n, hn⟩⟩ :=
    dense_iff_inter_open.mp hdense ((localResidueDegree K) '' U)
      (hopen U hU) hnonempty
  exact ⟨g', hg', ⟨⟨(g', Multiplicative.ofAdd n), hdeg.trans hn.symm⟩, rfl⟩⟩

theorem localWeilInertia_isOpen :
    IsOpen (((localWeilDegree K).toMonoidHom.ker : Subgroup (localWeilGroup K)) :
      Set (localWeilGroup K)) := by
  change IsOpen ((localWeilDegree K) ⁻¹' ({1} : Set (Multiplicative ℤ)))
  exact (isOpen_discrete _).preimage (localWeilDegree K).continuous

/-- The kernel of the discrete degree is the existing arithmetic inertia with its topology. -/
noncomputable def localWeilInertiaEquiv :
    (localResidueDatum K).inertia.toSubgroup ≃ₜ* (localWeilDegree K).toMonoidHom.ker := by
  let I := (localResidueDatum K).inertia.toSubgroup
  let J := (localWeilDegree K).toMonoidHom.ker
  let lift (i : I) : localWeilGroup K := ⟨(i.1, 1),
    (show localResidueDegree K i.1 = 1 from i.2).trans
      localWeilIntegerInclusion.map_one.symm⟩
  let forward (i : I) : J := ⟨lift i, rfl⟩
  let backward (x : J) : I := ⟨localWeilToAbsolute K x.1, by
    have hx : localWeilDegree K x.1 = 1 := x.2
    change localResidueDegree K (localWeilToAbsolute K x.1) = 1
    rw [localResidueDegree_localWeilToAbsolute K x.1, hx, map_one]⟩
  let e : I ≃* J := {
    toFun := forward
    invFun := backward
    left_inv := fun _ => rfl
    right_inv := fun x => by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (show localWeilDegree K x.1 = 1 from x.2).symm
    map_mul' := fun x y => by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (one_mul (1 : Multiplicative ℤ)).symm }
  have hcoe : Continuous (fun i : I => (i : Gal(SeparableClosure K/K))) :=
    continuous_subtype_val
  have hlift : Continuous lift := (hcoe.prodMk continuous_const).subtype_mk _
  have hinv : Continuous (fun x : J => localWeilToAbsolute K x.1) :=
    (localWeilToAbsolute K).continuous.comp continuous_subtype_val
  have hforward : Continuous forward := hlift.subtype_mk _
  have hbackward : Continuous backward := hinv.subtype_mk _
  exact
    { toMulEquiv := e
      continuous_toFun := hforward
      continuous_invFun := hbackward }

theorem localWeilInertia_isCompact :
    IsCompact (((localWeilDegree K).toMonoidHom.ker : Subgroup (localWeilGroup K)) :
      Set (localWeilGroup K)) := by
  let : CompactSpace (localResidueDatum K).inertia.toSubgroup :=
    Topology.IsClosedEmbedding.compactSpace
      (localResidueDatum K).inertia.isClosed'.isClosedEmbedding_subtypeVal
  have hcontinuous : Continuous (fun i => ((localWeilInertiaEquiv K i).1 : localWeilGroup K)) :=
    continuous_subtype_val.comp (localWeilInertiaEquiv K).continuous
  have hcompact := isCompact_univ.image hcontinuous
  rw [Set.image_univ] at hcompact
  have hrange :
      Set.range (fun i => ((localWeilInertiaEquiv K i).1 : localWeilGroup K)) =
        ((localWeilDegree K).toMonoidHom.ker : Set (localWeilGroup K)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (localWeilInertiaEquiv K i).2
    · intro hx
      obtain ⟨i, hi⟩ := (localWeilInertiaEquiv K).surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  rwa [hrange] at hcompact


/-- Inertia, with its original profinite topology, embeds as an open subgroup. -/
theorem localWeilInertia_isOpenEmbedding :
    Topology.IsOpenEmbedding
      (fun i => ((localWeilInertiaEquiv K i).1 : localWeilGroup K)) :=
  (localWeilInertia_isOpen K).isOpenEmbedding_subtypeVal.comp
    (localWeilInertiaEquiv K).toHomeomorph.isOpenEmbedding

private theorem map_closedCommutator_eq_of_denseRange_of_isClosed
    {W G : Type*} [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : W →ₜ* G) (hd : DenseRange f)
    (hc : IsClosed (((Subgroup.closedCommutator W).map f.toMonoidHom : Subgroup G) : Set G)) :
    (Subgroup.closedCommutator W).map f.toMonoidHom = Subgroup.closedCommutator G := by
  let C := (Subgroup.closedCommutator W).map f.toMonoidHom
  apply le_antisymm (Subgroup.closedCommutator_map_le f)
  refine Subgroup.topologicalClosure_minimal _ ?_ hc
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨a, b, rfl⟩
  have hcontinuous : Continuous (fun p : G × G => ⁅p.1, p.2⁆) := by
    change Continuous (fun p : G × G => p.1 * p.2 * p.1⁻¹ * p.2⁻¹)
    exact ((continuous_fst.mul continuous_snd).mul continuous_fst.inv).mul continuous_snd.inv
  apply hd.induction_on₂ (p := fun g h => ⁅g, h⁆ ∈ C) (hc.preimage hcontinuous) _ a b
  intro x y
  refine ⟨⁅x, y⁆, Subgroup.commutator_le_closedCommutator W ?_, ?_⟩
  · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  · exact map_commutatorElement f.toMonoidHom (g₁ := x) (g₂ := y)

/-- The Weil and absolute closures of the commutator have the same image in the
absolute Galois group, since the Weil commutator lies in compact inertia. -/
theorem localWeilToAbsolute_map_closedCommutator :
    (Subgroup.closedCommutator (localWeilGroup K)).map
        (localWeilToAbsolute K).toMonoidHom =
      Subgroup.closedCommutator Gal(SeparableClosure K / K) := by
  let W := localWeilGroup K
  let G := Gal(SeparableClosure K / K)
  let f : W →ₜ* G := localWeilToAbsolute K
  let C : Subgroup W := Subgroup.closedCommutator W
  have hkernel : C ≤ (localWeilDegree K).toMonoidHom.ker := by
    intro w hw
    have h := Subgroup.closedCommutator_map_le (localWeilDegree K)
      (show (localWeilDegree K w) ∈ C.map (localWeilDegree K).toMonoidHom from
        ⟨w, hw, rfl⟩)
    rw [Subgroup.closedCommutator_eq_bot_of_commGroup_t1] at h
    change localWeilDegree K w = 1
    exact Subgroup.mem_bot.mp h
  have hcompact : IsCompact (C : Set W) :=
    (localWeilInertia_isCompact K).of_isClosed_subset
      (Subgroup.isClosed_closedCommutator W) hkernel
  have hclosed : IsClosed ((C.map f.toMonoidHom : Subgroup G) : Set G) := by
    change IsClosed (f '' (C : Set W))
    exact (hcompact.image f.continuous).isClosed
  exact map_closedCommutator_eq_of_denseRange_of_isClosed f
    (localWeilToAbsolute_denseRange K) hclosed

/-- The canonical map of topological abelianizations induced by Weil inclusion. -/
noncomputable def localWeilAbelianizationToAbsolute :
    TopologicalAbelianization (localWeilGroup K) →ₜ*
      TopologicalAbelianization Gal(SeparableClosure K / K) :=
  TopologicalAbelianization.map (localWeilToAbsolute K)

theorem localWeilAbelianizationToAbsolute_injective :
    Function.Injective (localWeilAbelianizationToAbsolute K) := by
  let f := localWeilAbelianizationToAbsolute K
  apply (injective_iff_map_eq_one f.toMonoidHom).mpr
  intro q hq
  obtain ⟨w, rfl⟩ := TopologicalAbelianization.surjective_mk (localWeilGroup K) q
  have hw : localWeilToAbsolute K w ∈
      Subgroup.closedCommutator Gal(SeparableClosure K / K) := by
    apply TopologicalAbelianization.mk_eq_one_iff.mp
    exact hq
  rw [← localWeilToAbsolute_map_closedCommutator K] at hw
  obtain ⟨w', hw', heq⟩ := hw
  have h : w' = w := localWeilToAbsolute_injective K heq
  subst w'
  exact TopologicalAbelianization.mk_eq_one_iff.mpr hw'

/-- The integer degree descends to the same topological abelianization. -/
noncomputable def localWeilAbelianizationDegree :
    TopologicalAbelianization (localWeilGroup K) →ₜ* Multiplicative ℤ :=
  TopologicalAbelianization.lift (localWeilDegree K)


/-- Arithmetic residue degree on the existing absolute topological abelianization. -/
noncomputable def localAbsoluteAbelianResidueDegree :
    TopologicalAbelianization Gal(SeparableClosure K / K) →ₜ* ZHatMul :=
  TopologicalAbelianization.lift (localResidueDegree K)

/-- The Weil abelianization maps onto exactly the classes of integral residue degree. -/
theorem mem_range_localWeilAbelianizationToAbsolute_iff
    (a : TopologicalAbelianization Gal(SeparableClosure K/K)) :
    a ∈ (localWeilAbelianizationToAbsolute K).toMonoidHom.range ↔
      localAbsoluteAbelianResidueDegree K a ∈ localWeilIntegerInclusion.range := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := TopologicalAbelianization.surjective_mk (localWeilGroup K) w
    refine ⟨localWeilDegree K x, ?_⟩
    exact (localResidueDegree_localWeilToAbsolute K x).symm
  · rintro ⟨n, hn⟩
    obtain ⟨g, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure K / K) a
    let x : localWeilGroup K := ⟨(g, n), hn.symm⟩
    exact ⟨TopologicalAbelianization.mk (localWeilGroup K) x, rfl⟩

end LocalClassFieldTheory
