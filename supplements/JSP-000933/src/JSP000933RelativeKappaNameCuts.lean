import JSP000933RelativeKappaAntichainBound

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel BooleanCompletion MarkedForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def initialKappaGreedyValue (Q : ValuedPoset B N)
    (E : MixedEnumeration GroundContinuumSuccIndex N B) (x : TotalBA Q) (c : GroundContinuumSuccIndex) : TotalBA Q :=
  ⨆ i : ↥(Set.Iio c),⨆ n,traceRectangle Q n (greedyTraceWeight Q E x i.val n)

theorem initialKappaGreedyValue_le_r476 (Q : ValuedPoset B N)
    (E : MixedEnumeration GroundContinuumSuccIndex N B) (x : TotalBA Q) (c : GroundContinuumSuccIndex) :
    initialKappaGreedyValue Q E x c≤x := by
  apply iSup_le
  intro i
  apply iSup_le
  intro n
  exact (traceRectangle_accept_iff_r464 Q x n _).mpr
    (greedyTraceWeight_accepted_r465 Q E x i.val n)

theorem greedy_initial_on_kappaCut_r476 (Q : ValuedPoset B N)
    (E : MixedEnumeration GroundContinuumSuccIndex N B) (x : TotalBA Q) (c : GroundContinuumSuccIndex)
    (m : B) (hm : ∀ i,c≤ i → Disjoint m (greedyRowActive Q E x i)) :
    baseEmbed Q m⊓x=baseEmbed Q m⊓initialKappaGreedyValue Q E x c := by
  classical
  apply le_antisymm
  · calc
      baseEmbed Q m⊓x=baseEmbed Q m⊓greedyTraceValue Q E x :=
        congrArg (fun z => baseEmbed Q m⊓z) (greedyTraceValue_eq_r466 Q E x).symm
      _ ≤ _ := by
        unfold greedyTraceValue
        rw [inf_iSup_eq]
        apply iSup_le
        intro i
        rw [inf_iSup_eq]
        apply iSup_le
        intro n
        by_cases hi : i<c
        · exact le_inf inf_le_left (inf_le_right.trans (le_iSup_of_le (⟨i,hi⟩ : ↥(Set.Iio c))
            (le_iSup (fun k => traceRectangle Q k (greedyTraceWeight Q E x i k)) n)))
        · have h := (hm i (le_of_not_gt hi)).mono_right
            (show greedyTraceWeight Q E x i n≤greedyRowActive Q E x i from le_iSup _ n)
          rw [traceRectangle_disjoint_base_r467 Q n h]
          exact bot_le
  · exact inf_le_inf le_rfl (initialKappaGreedyValue_le_r476 Q E x c)

noncomputable def actualKappaCut_boundedFamilies {I : Type} (Q : ValuedPoset B N)
    (E : MixedEnumeration GroundContinuumSuccIndex N B) (x : I→TotalBA Q)
    (c : GroundContinuumSuccIndex) : B :=
  ⨅ i,⨆ b : ↥(Set.Iio c),(aboveKappaValue (greedyRowActive Q E (x i)) b.val)ᶜ

theorem actualKappaCuts_cover_r476 {I : Type} (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsSmallKappaNames B)
    (E : MixedEnumeration GroundContinuumSuccIndex N B) (x : I→TotalBA Q)
    (hI : Cardinal.mk I<GroundContinuumSucc) :
    (⨆ c,actualKappaCut_boundedFamilies Q E x c)=⊤ := by
  let F (i : I) (b : GroundContinuumSuccIndex) := (aboveKappaValue (greedyRowActive Q E (x i)) b)ᶜ
  have hF (i : I) : (⨆ b,F i b)=⊤ := by
    have h0 := relativeCCC_kappaAntichain_bounded_r475 Q hQ hB (greedyTraceWeight Q E (x i))
      (greedyTraceWeight_valid_r465 Q E (x i)) (greedyTraceWeight_apart_r465 Q E (x i))
    have hC := congrArg (fun z : B => zᶜ) h0
    change (unboundedKappaValue (greedyRowActive Q E (x i)))ᶜ = (⊥ : B)ᶜ at hC
    simpa only [unboundedKappaValue,F,compl_iInf,compl_bot] using hC
  exact top_unique ((le_iInf (fun i => (hF i).ge)).trans (hB I hI F))

theorem actualKappaCut_disjoint_r476 {I : Type} (Q : ValuedPoset B N)
    (E : MixedEnumeration GroundContinuumSuccIndex N B) (x : I→TotalBA Q)
    (c j : GroundContinuumSuccIndex) (hj : c≤j) (i : I) :
    Disjoint (actualKappaCut_boundedFamilies Q E x c) (greedyRowActive Q E (x i) j) := by
  apply le_compl_iff_disjoint_right.mp
  apply (iInf_le _ i).trans
  apply iSup_le
  intro b
  exact compl_le_compl (le_iSup (fun k : {k : GroundContinuumSuccIndex // b.val < k} => greedyRowActive Q E (x i) k.val)
    ⟨j,b.property.trans_le hj⟩)

theorem actualKappaCut_agrees_r476 {I : Type} (Q : ValuedPoset B N)
    (E : MixedEnumeration GroundContinuumSuccIndex N B) (x : I→TotalBA Q)
    (c : GroundContinuumSuccIndex) (m : B)
    (hm : m≤actualKappaCut_boundedFamilies Q E x c) (i : I) :
    baseEmbed Q m⊓x i=baseEmbed Q m⊓initialKappaGreedyValue Q E (x i) c :=
  greedy_initial_on_kappaCut_r476 Q E (x i) c m
    (fun j hj => (actualKappaCut_disjoint_r476 Q E x c j hj i).mono_left hm)

end RelativeOCA
end JSP000933
