import JSP000933RelativeDiscreteChoices

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]

abbrev SupportCandidate (I : Type) := OmegaOneIndex×Finset I

noncomputable def supportFiber (W : OmegaOneIndex→Finset I→B)
    (v : I) (i : OmegaOneIndex) : B :=
  ⨆ s : {s : Finset I // v∈s},W i s.val

open scoped Classical in
noncomputable def priorSupportBound (W : OmegaOneIndex→Finset I→B)
    (x : (SupportCandidate I)) (b : OmegaOneIndex) : B :=
  (if x.1≤b then ⊤ else ⊥)⊓(⨅ v : ↥x.2,(aboveValue (supportFiber W v.val) b)ᶜ)

theorem priorSupportBound_mono_c13 (W : OmegaOneIndex→Finset I→B)
    (x : (SupportCandidate I)) : Monotone (priorSupportBound W x) := by
  classical
  intro a b hab
  unfold priorSupportBound
  apply inf_le_inf
  · by_cases h : x.1≤a
    · simp only [ite_eq_left h,ite_eq_left (h.trans hab),le_rfl]
    · simp only [ite_eq_right h,bot_le]
  · exact le_iInf (fun v => (iInf_le _ v).trans
      (compl_le_compl (aboveValue_antitone_r431 (supportFiber W v.val) hab)))

theorem priorSupportBound_covers_c13 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset I→B) (m : B)
    (hF : ∀ v,m≤(unboundedValue (supportFiber W v))ᶜ) (x : (SupportCandidate I)) :
    m≤⨆ b,priorSupportBound W x b := by
  classical
  have h : m≤⨆ b : OmegaOneIndex,⨅ v : ↥x.2,(aboveValue (supportFiber W v.val) b)ᶜ :=
    uniform_countable_cutoffs_r444 hB m
      (fun v : ↥x.2 => fun b => (aboveValue (supportFiber W v.val) b)ᶜ)
      (fun v _ _ hab => compl_le_compl (aboveValue_antitone_r431 (supportFiber W v.val) hab))
      (fun v => (hF v.val).trans_eq (boundedValue_eq_join_r444 _))
  apply h.trans
  apply iSup_le
  intro b
  apply le_iSup_of_le (max b x.1)
  unfold priorSupportBound
  simp only [ite_eq_left (le_max_right b x.1),top_inf_eq]
  apply le_iInf
  intro v
  exact (iInf_le _ v).trans (compl_le_compl
    (aboveValue_antitone_r431 (supportFiber W v.val) (le_max_left b x.1)))

noncomputable def priorMixedSupportBound (W : OmegaOneIndex→Finset I→B) {m : B}
    (C : DiscreteChoiceOn (SupportCandidate I) m) (b : OmegaOneIndex) : B :=
  guardByChoice C (fun x => priorSupportBound W x b)

theorem priorMixedSupportBound_mono_c13 (W : OmegaOneIndex→Finset I→B) {m : B}
    (C : DiscreteChoiceOn (SupportCandidate I) m) : Monotone (priorMixedSupportBound W C) :=
  fun _ _ hab => guardByChoice_mono_r445 C (fun x => priorSupportBound_mono_c13 W x hab)

theorem priorMixedSupportBound_covers_c13 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset I→B) (m : B)
    (hF : ∀ v,m≤(unboundedValue (supportFiber W v))ᶜ)
    (C : DiscreteChoiceOn (SupportCandidate I) m) :
    m≤⨆ b,priorMixedSupportBound W C b :=
  guardByChoice_coversCutoffs_r445 C _ (fun x => (C.each_le x).trans
    (priorSupportBound_covers_c13 hB W m hF x))

end RelativeOCA
end JSP000933
