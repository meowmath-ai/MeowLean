import JSP000933RelativeGreedyTraces

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing CantorCodes

variable {B N I : Type} [CompleteBooleanAlgebra B]
variable [Preorder I] [WellFoundedLT I]

theorem greedyTraceValue_eq_r466 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) : greedyTraceValue Q E x=x := by
  classical
  let W := greedyTraceWeight Q E x
  let V := greedyTraceValue Q E x
  apply le_antisymm (greedyTraceValue_le_r465 Q E x)
  by_contra h
  have hNZ : x⊓Vᶜ≠⊥ := fun he =>
    h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hNZ
  have hCol : p.mask≤⨆ i,E.cell i p.trace := by rw [E.colFull]; exact le_top
  obtain ⟨i,b,hb,hbp,hbc⟩ :=
    exists_nonzero_below_choice_r135 p.mask p.nonzero (fun i => E.cell i p.trace) hCol
  let q : TotalCondition Q := ⟨b,p.trace,hb,hbp.trans p.valid⟩
  have hqp : q≤p := ⟨hbp,(hbp.trans p.valid).trans (Q.refl p.trace)⟩
  have hqV : imageCondition q≤Vᶜ := (imageCondition_mono_r50 hqp).trans (hp.trans inf_le_right)
  have hqx : imageCondition q≤x := (imageCondition_mono_r50 hqp).trans (hp.trans inf_le_left)
  have hQRect : imageCondition q=traceRectangle Q p.trace b := image_eq_base_meet_trace_r429 q
  have hAcc : b≤traceAccept Q x p.trace := (traceRectangle_accept_iff_r464 Q x _ _).mp
    (hQRect.symm.trans_le hqx)
  have hApart (j : ↥(Set.Iio i)) (k : N) :
      b≤(W j.val k⊓commonRefinementValue Q p.trace k)ᶜ := by
    have hOld : traceRectangle Q k (W j.val k)≤V :=
      le_iSup_of_le j.val (le_iSup (fun n => traceRectangle Q n (W j.val n)) k)
    have hZero : traceRectangle Q p.trace b⊓traceRectangle Q k (W j.val k)=⊥ := by
      rw [←hQRect]
      apply le_bot_iff.mp
      have hD : Disjoint Vᶜ V := disjoint_compl_left
      exact (inf_le_inf hqV hOld).trans (disjoint_iff_inf_le.mp hD)
    have ha : commonRefinementValue Q p.trace k⊓(b⊓W j.val k)=⊥ := by
      rw [← traceRectangle_pair_support_r464,hZero]
      exact (supportProjection_zero_iff_r428 Q ⊥).mpr rfl
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    calc
      b⊓(W j.val k⊓commonRefinementValue Q p.trace k)=
          commonRefinementValue Q p.trace k⊓(b⊓W j.val k) := by ac_rfl
      _ ≤ ⊥ := ha.le
  have hW : b≤W i p.trace := by
    change b≤greedyTraceWeight Q E x i p.trace
    rw [greedyTraceWeight_eq_r465 Q E x i]
    exact le_inf (le_inf hbc (le_inf q.valid hAcc)) (le_iInf (fun j => le_iInf (hApart j)))
  have hYes : imageCondition q≤V :=
    (hQRect.trans_le (traceRectangle_mono_r464 Q p.trace hW)).trans (le_iSup_of_le i (le_iSup (fun n => traceRectangle Q n (W i n)) p.trace))
  exact imageCondition_ne_bot_r50 q (disjoint_compl_right.out _ hYes hqV)

end RelativeOCA
end JSP000933
