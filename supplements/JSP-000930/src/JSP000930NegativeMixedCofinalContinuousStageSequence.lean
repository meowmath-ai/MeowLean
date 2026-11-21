import JSP000930NegativeNextGenuineMixedStage

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion

variable {B I : Type} [CompleteBooleanAlgebra B] [LinearOrder I]

structure MixedCofinalStageSequence (B I : Type) [CompleteBooleanAlgebra B] [LinearOrder I] where
  pick : OmegaOneIndex → DiscreteChoiceOn I (⊤ : B)
  increasing : ∀ i j,i < j → ∀ s t,¬ s < t → Disjoint ((pick i).value s) ((pick j).value t)
  cofinal : ∀ s,(⨆ j : OmegaOneIndex,⨆ t : {t : I // s < t},(pick j).value t.val) = ⊤
  limitAt : ∀ d,CheckedOmegaOneLimit d → ∀ t,(pick d).value t ≠ ⊥ → CheckedGroundLimit t
  continuous : ∀ d,CheckedOmegaOneLimit d → ∀ t s,s < t →
    (pick d).value t ≤ chosenHigherBefore (fun r : PriorOmega d => pick r.val) s

theorem omegaOne_next_nonlimit (d : OmegaOneIndex) :
    ∃ e,d < e ∧ ¬ CheckedOmegaOneLimit e := by
  let A : Set OmegaOneIndex := {e | d < e}
  obtain ⟨a,ha⟩ := OmegaOneIndex_countable_bounded_r61 {d} (Set.countable_singleton d)
  obtain ⟨e,he,hMin⟩ := wellFounded_lt.has_min A ⟨a,ha d (Set.mem_singleton d)⟩
  refine ⟨e,he,?_⟩
  rintro ⟨f,hf,hTop,hCof⟩
  obtain ⟨n,hn⟩ := hCof d he
  exact hMin (f n) hn (hTop n)

variable {P : Type} [Preorder P] [WellFoundedLT I] [Nonempty I]

theorem exists_mixedCofinalStageSequence (hP : IsCountablyClosed P)
    (hI : AllCountableGroundBounded I)
    (E : MixedEnumeration OmegaOneIndex I (RO P)) :
    Nonempty (MixedCofinalStageSequence (RO P) I) := by
  classical
  let D (j : OmegaOneIndex) : DiscreteChoiceOn I (⊤ : RO P) :=
    ⟨E.cell j,E.rowApart j,fun _ => le_top,E.rowFull j⟩
  let G := DiscreteChoiceOn I (⊤ : RO P)
  let old (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i < j → G) :
      PriorOmega j → G :=
    fun i => prev i.val i.property
  have hExist (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i < j → G)
      (h : PriorStageCoherent (old j prev)) :
      ∃ c : G,∀ t,c.value t ≤ nextMixedStageValue D j (old j prev) t :=
    exists_discreteChoiceOn_r445 ⊤ _ (nextMixedStage_cover hP hI D j (old j prev) h)
  let step (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i < j → G) : G :=
    if h : PriorStageCoherent (old j prev) then Classical.choose (hExist j prev h) else D j
  let C : OmegaOneIndex → G := WellFounded.fix wellFounded_lt step
  have hC (j : OmegaOneIndex) : C j = step j (fun i _ => C i) :=
    WellFounded.fix_eq wellFounded_lt step j
  let Sep (j : OmegaOneIndex) : Prop :=
    ∀ i < j,∀ s t,¬ s < t → Disjoint ((C i).value s) ((C j).value t)
  have hSep : ∀ j,Sep j := by
    intro j
    refine wellFounded_lt.induction (C := Sep) j ?_
    intro j ih i hi s t hst
    have hPrev : PriorStageCoherent (old j (fun i _ => C i)) := by
      intro a b hab u v huv
      exact ih b.val b.property a.val hab u v huv
    have hChosen : (C j).value t ≤ nextMixedStageValue D j (old j (fun i _ => C i)) t := by
      rw [hC j]
      change (if h : PriorStageCoherent (old j (fun i _ => C i)) then
        Classical.choose (hExist j (fun i _ => C i) h) else D j).value t ≤ _
      rw [dite_eq_left hPrev]
      exact Classical.choose_spec (hExist j (fun i _ => C i) hPrev) t
    have hGuard : (C j).value t ≤ guardStageBelow (C i) t :=
      hChosen.trans (inf_le_left.trans (iInf_le _ (⟨i,hi⟩ : PriorOmega j)))
    exact guardStageBelow_apart hst hGuard
  have hGood (j : OmegaOneIndex) (t : I) :
      (C j).value t ≤ nextMixedStageValue D j (fun i : PriorOmega j => C i.val) t := by
    have hPrev : PriorStageCoherent (old j (fun i _ => C i)) := by
      intro a b hab u v huv
      exact hSep b.val a.val hab u v huv
    rw [hC j]
    change (if h : PriorStageCoherent (old j (fun i _ => C i)) then
      Classical.choose (hExist j (fun i _ => C i) h) else D j).value t ≤ _
    rw [dite_eq_left hPrev]
    exact Classical.choose_spec (hExist j (fun i _ => C i) hPrev) t
  refine ⟨⟨C,fun i j h => hSep j i h,?_,?_,?_⟩⟩
  · intro s
    apply top_unique
    apply (E.colFull s).ge.trans
    apply iSup_le
    intro j
    obtain ⟨d,hjd,hd⟩ := omegaOne_next_nonlimit j
    have hGuard (t : I) : (C d).value t ≤ guardStageBelow (D j) t := by
      have he := hGood d t
      rw [nextMixedStageValue,ite_eq_right hd] at he
      exact he.trans (inf_le_right.trans (iInf_le _ (⟨j,hjd.le⟩ : ThroughOmega d)))
    change (D j).value s ≤ _
    have hCover : (D j).value s ≤ (D j).value s ⊓ ⨆ t, (C d).value t :=
      le_inf le_rfl (le_top.trans (C d).covers.ge)
    apply hCover.trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro t
    by_cases ht : s < t
    · exact inf_le_right.trans (le_iSup_of_le d
        (le_iSup (fun t : {t : I // s < t} => (C d).value t.val) ⟨t,ht⟩))
    · exact (disjoint_iff_inf_le.mp (guardStageBelow_apart ht (hGuard t))).trans bot_le
  · intro d hd t ht
    by_contra h
    have he := hGood d t
    rw [nextMixedStageValue,ite_eq_left hd,ite_eq_right h,inf_bot_eq] at he
    exact ht (le_bot_iff.mp he)
  · intro d hd t s hs
    have he := hGood d t
    by_cases ht : CheckedGroundLimit t
    · rw [nextMixedStageValue,ite_eq_left hd,ite_eq_left ht] at he
      exact he.trans (inf_le_right.trans (iInf_le _ (⟨s,hs⟩ : {s : I // s < t})))
    · rw [nextMixedStageValue,ite_eq_left hd,ite_eq_right ht,inf_bot_eq] at he
      exact he.trans bot_le

end JSP000930.Negative
