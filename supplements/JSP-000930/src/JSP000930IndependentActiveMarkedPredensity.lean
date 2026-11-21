import JSP000930DensePredensityConjugacy

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.ForcingTransport

variable {B C N M : Type} [NontrivialCompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

def changeValuedBaseCondition930 (F : CompleteValueMap B C) (Q : ValuedPoset B M)
    (p : TotalCondition Q) : TotalCondition (changeValuedBase F Q) :=
  ⟨F.toFun p.mask,p.trace,
    fun h => p.nonzero (F.injective (h.trans F.map_bot.symm)),F.monotone p.valid⟩

theorem changeValuedBaseCondition_mono930 (F : CompleteValueMap B C) (Q : ValuedPoset B M) :
    Monotone (changeValuedBaseCondition930 F Q) := fun _ _ h =>
  ⟨F.monotone h.1,F.monotone h.2⟩

def changeValuedBaseMasked930 (F : CompleteValueMap B C) (Q : ValuedPoset B M) (m : B)
    (p : MaskedCondition Q m) : MaskedCondition (changeValuedBase F Q) (F.toFun m) :=
  ⟨changeValuedBaseCondition930 F Q p.val,F.monotone p.property⟩

theorem changeValuedBaseMasked_mono930 (F : CompleteValueMap B C) (Q : ValuedPoset B M) (m : B) :
    Monotone (changeValuedBaseMasked930 F Q m) := fun _ _ h =>
  changeValuedBaseCondition_mono930 F Q h

theorem image_weakest_eq_base930 (P : ValuedPoset B N) (m : B) (hm : m≠⊥) :
    imageCondition (weakenToBase P m hm) = baseEmbed P m := by
  apply le_antisymm
  · exact (baseEmbed_reflects_mask_r427 _ _).mpr le_rfl
  · apply le_of_image_tests
    intro q hq
    exact imageCondition_mono_r50 ((below_weakenToBase_r426 q hm).mpr
      ((baseEmbed_reflects_mask_r427 _ _).mp hq))

def pairKeepOnlyRight930 (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (p : TotalCondition Q) : TotalCondition (valuedPair P Q) :=
  ⟨p.mask,(P.weakest,p.trace),p.nonzero,
    le_inf (le_top.trans_eq P.weakest_valid.symm) p.valid⟩

theorem pairSecond_le_iff930 (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (p : TotalCondition (valuedPair P Q)) (q : TotalCondition Q) :
    pairSecond930 P Q p ≤ q ↔ p ≤ pairKeepOnlyRight930 P Q q := by
  constructor
  · intro h
    exact ⟨h.1,le_inf ((p.valid.trans inf_le_left).trans (P.weaker _)) h.2⟩
  · intro h
    exact ⟨h.1,h.2.trans inf_le_right⟩

theorem pairToIterated_keepRight930 (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (p : TotalCondition Q) :
    pairToIterated P Q (pairKeepOnlyRight930 P Q p) =
      changeValuedBaseCondition930 (markedCompleteValueMap P) Q p := by
  apply totalCondition_eq_of_data
  · change imageCondition (weakenToBase P p.mask p.nonzero) = baseEmbed P p.mask
    exact image_weakest_eq_base930 P p.mask p.nonzero
  · rfl

theorem independentActiveRow_marked_predensity930 (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (m : B) :
    PreservesPredensity (changeValuedBaseMasked930 (markedCompleteValueMap P) Q m) := by
  intro X hX q
  let F := markedCompleteValueMap P
  let G := pairIteratedDenseMap P Q
  obtain ⟨p,hp⟩ := G.dense q.val
  have hm : p.mask ≤ m := (baseEmbed_reflects_mask_r427 (pairFirst P Q p) m).mp
    (hp.1.trans q.property)
  let r : MaskedCondition Q m := ⟨pairSecond930 P Q p,hm⟩
  obtain ⟨d,hd,hdX⟩ := hX r
  obtain ⟨p',hp',hp'D⟩ := (pairSecondRestriction P Q).lift p d.val hd
  have hHit : p'≤pairKeepOnlyRight930 P Q d.val :=
    (pairSecond_le_iff930 P Q p' d.val).mp hp'D
  have hQ : G.map p'≤q.val := (G.monotone hp').trans hp
  have hD := G.monotone hHit
  change G.map p' ≤ pairToIterated P Q (pairKeepOnlyRight930 P Q d.val) at hD
  rw [pairToIterated_keepRight930] at hD
  exact ⟨d,hdX,⟨G.map p',hQ.1.trans q.property⟩,hQ,hD⟩

end JSP000930.Negative
