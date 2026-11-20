import JSP000933MaskProjectedCCC
import JSP000933NativeSuccessorPreservation

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport RelativeOCA MarkedForcing OpenGraphForcing

noncomputable def orderIsoDenseForcingMap {P Q : Type} [Preorder P] [Preorder Q]
    (F : P ≃o Q) : DenseForcingMap P Q where
  map := F
  monotone := F.monotone
  dense q := ⟨F.symm q,by simp⟩
  reflect_compatible := by
    intro p p' h
    obtain ⟨q,hq,hq'⟩ := h
    exact ⟨F.symm q,by simpa using F.symm.monotone hq,
      by simpa using F.symm.monotone hq'⟩

theorem orderIso_dense_pull_reduction {P Q : Type} [Preorder P] [Preorder Q]
    (F : P ≃o Q) (c : RO Q) :
    (orderIsoDenseForcingMap F).pullIso c = (orderIsoReduction F).boolPullback c := by
  apply le_antisymm
  · apply le_of_image_tests
    intro p hp
    rw [image_le_regular_pullback]
    rw [image_le_iff_member] at hp ⊢
    exact hp
  · apply le_of_image_tests
    intro p hp
    rw [image_le_regular_pullback] at hp
    rw [image_le_iff_member] at hp ⊢
    exact hp

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

theorem basedPrefix_base_commutes (tail : BasedTailPolicy A B T) {a b : A}
    (ha : (⊥ : A)<a) (hab : a≤b) (x : B) :
    (prefixReduction hab).boolPullback ((prefixMaskRealization tail ha).embed x) =
      (prefixMaskRealization tail (ha.trans_le hab)).embed x := by
  have htest (p : BasedBefore tail b) :
      imageCondition p ≤ (prefixReduction hab).boolPullback ((prefixMaskRealization tail ha).embed x)
      ↔ imageCondition p ≤ (prefixMaskRealization tail (ha.trans_le hab)).embed x := by
    rw [image_le_regular_pullback,MaskRealization.image_le_iff,MaskRealization.image_le_iff]
    change baseMask tail (restrict p.val a).val ≤ x ↔ baseMask tail p.val ≤ x
    rw [baseMask_restrict tail p.val ha]
  exact le_antisymm (le_of_image_tests (fun p => (htest p).mp))
    (le_of_image_tests (fun p => (htest p).mpr))

theorem basedPrefix_successor_projectedCCC
    (tail : BasedTailPolicy A B T) {a b : A} (ha : (⊥ : A)<a)
    (hVa : Monotone (TailStageValues tail (a := a)))
    (hTop : TailStageValues tail (a := a) ⊤ = ⊤)
    (succ : ∀ i : A, i < b ↔ i ≤ a)
    (hPrev : ProjectedAntichainCCC (prefixMaskRealization tail ha).project)
    (hCCC : ForcesRelativeCCC (ExactTailIterand tail hVa hTop)) :
    ProjectedAntichainCCC (prefixMaskRealization tail (ha.trans ((succ a).mpr le_rfl))).project := by
  let Q := ExactTailIterand tail hVa hTop
  let F := (orderIsoDenseForcingMap (prefixOrderIso_r85 (basedPolicy tail) a)).pullIso
  let G := markedSuccessorPullIso tail (ne_of_gt ha) hVa hTop succ
  let M := prefixMaskRealization tail ha
  let M' := prefixMaskRealization tail (ha.trans ((succ a).mpr le_rfl))
  have hπGC : GaloisConnection (M.project ∘ F) (F.symm ∘ M.embed) :=
    fun x y => by
      change M.project (F x) ≤ y ↔ x ≤ F.symm (M.embed y)
      exact (M.project_gc _ _).trans F.le_symm_apply.symm
  have hπ (v : OmegaOneIndex → PreStageAlgebra tail (a := a))
      (hv : ∀ i j,i<j → Disjoint (v i) (v j)) :
      unboundedValue (fun i => (M.project ∘ F) (v i)) = ⊥ := by
    apply hPrev
    intro i j hij
    apply disjoint_iff_inf_le.mpr
    rw [←F.map_inf,←F.map_bot]
    exact F.monotone (disjoint_iff_inf_le.mp (hv i j hij))
  have hComposed :
      ProjectedAntichainCCC (M.project ∘ F ∘ supportProjection Q) :=
    projectedAntichainCCC_comp (M.project ∘ F) (supportProjection Q) hπGC.monotone_l
      (fun _ f => hπGC.l_iSup) hπ (relativeCCC_projectedAntichain_bounded_r434 Q hCCC)
  have hEq (x : RO (BasedBefore tail b)) :
      M'.project x = (M.project ∘ F ∘ supportProjection Q) (G.symm x) := by
    have hAdj (z : B) : M'.project x≤z ↔ (M.project ∘ F ∘ supportProjection Q) (G.symm x)≤z := by
      rw [M'.project_gc]
      change x≤M'.embed z ↔ (M.project ∘ F) (supportProjection Q (G.symm x))≤z
      rw [hπGC]
      change _ ↔ supportProjection Q (G.symm x) ≤ F.symm (M.embed z)
      rw [supportProjection_le_iff_r428,←G.le_iff_le,G.apply_symm_apply,
        markedSuccessor_base_commutes,←orderIso_dense_pull_reduction]
      change x ≤ M'.embed z ↔ x ≤ (prefixReduction (((succ a).mpr le_rfl).le)).boolPullback
        (F (F.symm (M.embed z)))
      rw [F.apply_symm_apply,basedPrefix_base_commutes tail ha]
    exact le_antisymm ((hAdj _).mpr le_rfl) ((hAdj _).mp le_rfl)
  intro v hv
  change unboundedValue (fun i => M'.project (v i)) = ⊥
  rw [show (fun i => M'.project (v i)) =
    (fun i => (M.project ∘ F ∘ supportProjection Q) (G.symm (v i))) from funext (fun i => hEq (v i))]
  apply hComposed
  intro i j hij
  apply disjoint_iff_inf_le.mpr
  rw [←G.symm.map_inf,←G.symm.map_bot]
  exact G.symm.monotone (disjoint_iff_inf_le.mp (hv i j hij))

end ForcingTransport
end JSP000933
