import JSP000933RelativeTraceRankBounds

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing CantorCodes OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def rankedInitialGreedy (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (rank : N→OmegaOneIndex)
    (x : TotalBA Q) (c b : OmegaOneIndex) : TotalBA Q :=
  ⨆ i : ↥(Set.Iio c),⨆ n : {n : N // rank n<b},
    traceRectangle Q n.val (greedyTraceWeight Q E x i.val n.val)

theorem rankedInitialGreedy_onMask_r487 (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (rank : N→OmegaOneIndex)
    (x : TotalBA Q) (c b : OmegaOneIndex) (m : B)
    (hm : m≤allTraceRanksBelow E rank c b) :
    baseEmbed Q m⊓initialGreedyValue Q E x c=baseEmbed Q m⊓rankedInitialGreedy Q E rank x c b := by
  classical
  apply le_antisymm
  · unfold initialGreedyValue
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    by_cases hn : rank n<b
    · exact le_inf inf_le_left (inf_le_right.trans
        (le_iSup_of_le i (le_iSup (fun k : {k : N // rank k < b} =>
          traceRectangle Q k.val (greedyTraceWeight Q E x i.val k.val)) ⟨n,hn⟩)))
    · have hD := (allTraceRanksBelow_disjoint_r486 E rank c b i.val i.property n
        (le_of_not_gt hn)).mono_left hm
      have hW := hD.mono_right (greedyTraceWeight_cell_r465 Q E x i.val n)
      rw [traceRectangle_disjoint_base_r467 Q n hW]
      exact bot_le
  · apply inf_le_inf le_rfl
    apply iSup_le
    intro i
    apply iSup_le
    intro n
    exact le_iSup_of_le i (le_iSup (fun k => traceRectangle Q k (greedyTraceWeight Q E x i.val k)) n.val)

theorem local_rankedRealNames_r487 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex N B) (rank : N→OmegaOneIndex)
    (x : ℕ→TotalBA Q) (p : TotalBA Q) (hp : p≠⊥) :
    ∃ (c b : OmegaOneIndex) (m : B) (r : TotalCondition Q),
      m≠⊥ ∧ imageCondition r≤p⊓baseEmbed Q m ∧
      ∀ n,baseEmbed Q m⊓x n=baseEmbed Q m⊓rankedInitialGreedy Q E rank (x n) c b := by
  let v := supportProjection Q p
  have hv : v≠⊥ := fun he => hp ((supportProjection_zero_iff_r428 Q p).mp he)
  let C := actualGreedyCut Q E x
  have hTop : (⨆ c,C c)=⊤ := actualGreedyCuts_cover_r468 Q hQ hB E x
  obtain ⟨c,m0,hm0,hmv,hmC⟩ := exists_nonzero_below_choice_r135 v hv C
    (hTop.symm ▸ le_top)
  let D := allTraceRanksBelow E rank c
  have hd : (⨆ b,D b)=⊤ := allTraceRanksBelow_cover_r486 hB E rank c
  obtain ⟨b,m,hm,hm0',hmD⟩ := exists_nonzero_below_choice_r135 m0 hm0 D
    (hd.symm ▸ le_top)
  have hSub : m ≤ supportProjection Q p := hm0'.trans hmv
  have hN : p⊓baseEmbed Q m≠⊥ := by
    intro he
    have hS := supportProjection_meet_base_r428 Q p m
    rw [he,(supportProjection_zero_iff_r428 Q ⊥).mpr rfl,inf_eq_right.mpr hSub] at hS
    exact hm hS.symm
  obtain ⟨r,hr⟩ := imageCondition_dense_r50 _ hN
  refine ⟨c,b,m,r,hm,hr,fun n => ?_⟩
  exact (greedy_initial_on_cut_r467 Q E (x n) c m (fun i hi =>
    (actualGreedyCut_disjoint_r468 Q E x c i hi n).mono_left (hm0'.trans hmC))).trans
      (rankedInitialGreedy_onMask_r487 Q E rank (x n) c b m hmD)

end RelativeOCA
end JSP000933
