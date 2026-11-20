import JSP000933RelativeDiscreteChoices

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

abbrev LabelCandidate := OmegaOneIndex×Finset OmegaOneIndex

noncomputable def vertexFiber (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (v i : OmegaOneIndex) : B :=
  ⨆ s : {s : Finset OmegaOneIndex // v∈s},W i s.val

open scoped Classical in
noncomputable def priorLabelBound (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (x : LabelCandidate) (b : OmegaOneIndex) : B :=
  (if x.1≤b then ⊤ else ⊥)⊓(⨅ v : ↥x.2,(aboveValue (vertexFiber W v.val) b)ᶜ)

theorem priorLabelBound_mono_r446 (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (x : LabelCandidate) : Monotone (priorLabelBound W x) := by
  classical
  intro a b hab
  unfold priorLabelBound
  apply inf_le_inf
  · by_cases h : x.1≤a
    · simp only [ite_eq_left h,ite_eq_left (h.trans hab),le_rfl]
    · simp only [ite_eq_right h,bot_le]
  · exact le_iInf (fun v => (iInf_le _ v).trans
      (compl_le_compl (aboveValue_antitone_r431 (vertexFiber W v.val) hab)))

theorem priorLabelBound_covers_r446 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (m : B)
    (hF : ∀ v,m≤(unboundedValue (vertexFiber W v))ᶜ) (x : LabelCandidate) :
    m≤⨆ b,priorLabelBound W x b := by
  classical
  have h : m≤⨆ b : OmegaOneIndex,⨅ v : ↥x.2,(aboveValue (vertexFiber W v.val) b)ᶜ :=
    uniform_countable_cutoffs_r444 hB m
      (fun v : ↥x.2 => fun b => (aboveValue (vertexFiber W v.val) b)ᶜ)
      (fun v _ _ hab => compl_le_compl (aboveValue_antitone_r431 (vertexFiber W v.val) hab))
      (fun v => (hF v.val).trans_eq (boundedValue_eq_join_r444 _))
  apply h.trans
  apply iSup_le
  intro b
  apply le_iSup_of_le (max b x.1)
  unfold priorLabelBound
  simp only [ite_eq_left (le_max_right b x.1),top_inf_eq]
  apply le_iInf
  intro v
  exact (iInf_le _ v).trans (compl_le_compl
    (aboveValue_antitone_r431 (vertexFiber W v.val) (le_max_left b x.1)))

noncomputable def priorMixedLabelBound (W : OmegaOneIndex→Finset OmegaOneIndex→B) {m : B}
    (C : DiscreteChoiceOn LabelCandidate m) (b : OmegaOneIndex) : B :=
  guardByChoice C (fun x => priorLabelBound W x b)

theorem priorMixedLabelBound_mono_r446 (W : OmegaOneIndex→Finset OmegaOneIndex→B) {m : B}
    (C : DiscreteChoiceOn LabelCandidate m) : Monotone (priorMixedLabelBound W C) :=
  fun _ _ hab => guardByChoice_mono_r445 C (fun x => priorLabelBound_mono_r446 W x hab)

theorem priorMixedLabelBound_covers_r446 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (m : B)
    (hF : ∀ v,m≤(unboundedValue (vertexFiber W v))ᶜ)
    (C : DiscreteChoiceOn LabelCandidate m) :
    m≤⨆ b,priorMixedLabelBound W C b :=
  guardByChoice_coversCutoffs_r445 C _ (fun x => (C.each_le x).trans
    (priorLabelBound_covers_r446 hB W m hF x))

end RelativeOCA
end JSP000933
