import JSP000930NegativeCountableMixedGroundStageProfiles

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion
  JSP000933.CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B] [LinearOrder I]

abbrev PriorOmega (d : OmegaOneIndex) := {j : OmegaOneIndex // j < d}

abbrev ThroughOmega (d : OmegaOneIndex) := {j : OmegaOneIndex // j ≤ d}

instance (d : OmegaOneIndex) : Countable (ThroughOmega d) := by
  obtain ⟨e,he⟩ := OmegaOneIndex_countable_bounded_r61 {d} (Set.countable_singleton d)
  letI : Countable (PriorOmega e) := OmegaOneIndex_initial_countable_r61 e
  let f : ThroughOmega d → PriorOmega e := fun j =>
    ⟨j.val,j.property.trans_lt (he d (Set.mem_singleton d))⟩
  exact (show Function.Injective f from fun _ _ h =>
    Subtype.ext (congrArg (fun j : PriorOmega e => j.val) h)).countable

def PriorStageCoherent {d : OmegaOneIndex} (C : PriorOmega d → DiscreteChoiceOn I (⊤ : B)) : Prop :=
  ∀ i j,i < j → ∀ s t,¬ s < t → Disjoint ((C i).value s) ((C j).value t)

open scoped Classical in
noncomputable def guardStageBelow (C : DiscreteChoiceOn I (⊤ : B)) (t : I) : B :=
  guardByChoice C (fun s => if s < t then ⊤ else ⊥)

noncomputable def chosenHigherBefore {d : OmegaOneIndex}
    (C : PriorOmega d → DiscreteChoiceOn I (⊤ : B)) (s : I) : B :=
  ⨆ j : PriorOmega d,⨆ t : {t : I // s < t},(C j).value t.val

open scoped Classical in
noncomputable def nextMixedStageValue (E : OmegaOneIndex → DiscreteChoiceOn I (⊤ : B))
    (d : OmegaOneIndex) (C : PriorOmega d → DiscreteChoiceOn I (⊤ : B)) (t : I) : B :=
  (⨅ j : PriorOmega d,guardStageBelow (C j) t) ⊓
    if CheckedOmegaOneLimit d then
      (if CheckedGroundLimit t then (⨅ s : {s : I // s < t},chosenHigherBefore C s.val) else ⊥)
    else (⨅ j : ThroughOmega d,guardStageBelow (E j.val) t)

theorem guardStageBelow_from_decided {C : DiscreteChoiceOn I (⊤ : B)}
    {x t : I} {p : B} (hx : x < t) (hp : p ≤ C.value x) :
    p ≤ guardStageBelow C t := by
  unfold guardStageBelow
  have h := guardByChoice_onCell_r445 C (fun s => if s < t then (⊤ : B) else ⊥) x
  exact hp.trans (by simpa only [ite_eq_left hx,inf_top_eq] using h)

theorem guardStageBelow_apart {C : DiscreteChoiceOn I (⊤ : B)}
    {x t : I} {p : B} (hx : ¬ x < t) (hp : p ≤ guardStageBelow C t) :
    Disjoint (C.value x) p := by
  apply disjoint_iff_inf_le.mpr
  rw [inf_comm]
  have h := (inf_le_inf hp le_rfl).trans
    (guardByChoice_elim_r445 C (fun s => if s < t then (⊤ : B) else ⊥) x)
  simpa only [ite_eq_right hx] using h

variable {P : Type} [Preorder P]
variable [WellFoundedLT I] [Nonempty I]

theorem checkedOmega_prior_nonempty_noMax {d : OmegaOneIndex}
    (hd : CheckedOmegaOneLimit d) :
    Nonempty (PriorOmega d) ∧ ∀ j : PriorOmega d,∃ k : PriorOmega d,j < k := by
  obtain ⟨f,hf,hTop,hCof⟩ := hd
  refine ⟨⟨⟨f 0,hTop 0⟩⟩,fun j => ?_⟩
  obtain ⟨n,hn⟩ := hCof j.val j.property
  exact ⟨⟨f n,hTop n⟩,hn⟩

theorem nextMixedStage_cover (hP : IsCountablyClosed P) (hI : AllCountableGroundBounded I)
    (E : OmegaOneIndex → DiscreteChoiceOn I (⊤ : RO P))
    (d : OmegaOneIndex) (C : PriorOmega d → DiscreteChoiceOn I (⊤ : RO P))
    (hC : PriorStageCoherent C) :
    (⊤ : RO P) ≤ ⨆ t,nextMixedStageValue E d C t := by
  classical
  letI : Countable (PriorOmega d) := OmegaOneIndex_initial_countable_r61 d
  let S := ⨆ t,nextMixedStageValue E d C t
  change (⊤ : RO P) ≤ S
  by_contra hn
  have hP₀ : Sᶜ ≠ ⊥ := fun he => hn (compl_eq_bot.mp he).ge
  have h1 : Sᶜ ≤ ⨆ f : PriorOmega d → I,⨅ j,(C j).value (f j) :=
    le_top.trans (countable_mixed_profiles_cover hP C).ge
  obtain ⟨f,p,hp,hpS,hpf⟩ := exists_nonzero_below_choice_r135 Sᶜ hP₀
    (fun f : PriorOmega d → I => ⨅ j,(C j).value (f j)) h1
  have hf (j : PriorOmega d) : p ≤ (C j).value (f j) := hpf.trans (iInf_le _ j)
  have hStrict : StrictMono f := by
    intro j k hjk
    by_contra h
    exact hp ((hC j k hjk _ _ h).out _ (hf j) (hf k))
  by_cases hd : CheckedOmegaOneLimit d
  · have H := checkedOmega_prior_nonempty_noMax hd
    letI : Nonempty (PriorOmega d) := H.1
    obtain ⟨t,ht,hFt,hCof⟩ := actual_limit_of_profile hI H.2 f hStrict
    have hU : p ≤ nextMixedStageValue E d C t := by
      unfold nextMixedStageValue
      rw [ite_eq_left hd,ite_eq_left ht]
      refine le_inf (le_iInf (fun j => guardStageBelow_from_decided (hFt j) (hf j))) ?_
      apply le_iInf
      intro s
      obtain ⟨j,hj⟩ := hCof s.val s.property
      exact (hf j).trans (le_iSup_of_le j
        (le_iSup (fun z : {z : I // s.val < z} => (C j).value z.val) ⟨f j,hj⟩))
    exact hp (disjoint_compl_right.out _ (hU.trans (le_iSup _ t)) hpS)
  · let D (j : ThroughOmega d) := E j.val
    have hdCov : p ≤ ⨆ f : ThroughOmega d → I,⨅ j,(D j).value (f j) :=
      le_top.trans (countable_mixed_profiles_cover hP D).ge
    obtain ⟨g,q,hq,hqp,hqg⟩ := exists_nonzero_below_choice_r135 p hp
      (fun g : ThroughOmega d → I => ⨅ j,(D j).value (g j)) hdCov
    let h : PriorOmega d ⊕ ThroughOmega d → I := Sum.elim f g
    obtain ⟨t,ht⟩ := all_countable_groundProfiles_bounded hI h
    have hU : q ≤ nextMixedStageValue E d C t := by
      unfold nextMixedStageValue
      rw [ite_eq_right hd]
      refine le_inf (le_iInf (fun j => ?_)) (le_iInf (fun j => ?_))
      · exact guardStageBelow_from_decided (ht (Sum.inl j)) (hqp.trans (hf j))
      · exact guardStageBelow_from_decided (ht (Sum.inr j)) (hqg.trans (iInf_le _ j))
    exact hq (disjoint_compl_right.out _ (hU.trans (le_iSup _ t)) (hqp.trans hpS))

end JSP000930.Negative
