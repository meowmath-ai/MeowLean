import JSP000933RelativeKappaAntichainBound
import JSP000933RelativeChoiceNormalization

open Cardinal

namespace JSP000930.Positive

open JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.PreparedModel JSP000933.RelativeOCA

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem relativeCCC_projectedKappaAntichain_bounded_p10 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsSmallKappaNames B)
    (V : GroundContinuumSuccIndex→TotalBA Q)
    (hV : ∀ i j,i<j→Disjoint (V i) (V j)) :
    unboundedKappaValue (fun i => supportProjection Q (V i))=⊥ := by
  have h := relativeCCC_kappaAntichain_bounded_r475 Q hQ hB (fun i => traceWeight Q (V i))
    (fun i n => traceWeight_le_valid_r434 Q (V i) n)
    (fun i j hij n k => traceWeights_incompatible_of_disjoint_r434 Q (hV i j hij) n k)
  simpa only [traceWeight_joins_projection_r434] using h

theorem relativeCCC_preserves_boundsSmallKappa_p10 (Q : ValuedPoset B N)
    (hB : BoundsSmallKappaNames B) (hQ : ForcesRelativeCCC Q) :
    BoundsSmallKappaNames (TotalBA Q) := by
  intro I hI V
  let C (n : I) := firstChoiceCell (V n)
  let W (n : I) (i : GroundContinuumSuccIndex) := supportProjection Q (C n i)
  let F (n : I) (a : GroundContinuumSuccIndex) := (aboveKappaValue (W n) a)ᶜ
  have hCovered (n : I) : (⨆ a,F n a)=⊤ := by
    have hh := relativeCCC_projectedKappaAntichain_bounded_p10 Q hQ hB (C n)
      (fun i j h => firstChoiceCell_disjoint_r435 (V n) i j h)
    have hc := congrArg (fun x : B => xᶜ) hh
    simpa only [unboundedKappaValue,compl_iInf,compl_bot,W,F] using hc
  let G (b : GroundContinuumSuccIndex) : B :=
    ⨅ n,⨆ a : {a : GroundContinuumSuccIndex // a < b},F n a.val
  have hG : (⨆ b,G b)=⊤ :=
    top_unique ((le_iInf (fun n => (hCovered n).ge)).trans (hB I hI F))
  let m : TotalBA Q := ⨅ n,⨆ i,V n i
  have hM : m ≤ m ⊓(⨆ b,baseEmbed Q (G b)) := by
    rw [← baseEmbed_joins_r427,hG,baseEmbed_top_r427,inf_top_eq]
  apply hM.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro b
  apply le_iSup_of_le b
  apply le_iInf
  intro n
  let t := m⊓baseEmbed Q (G b)
  have hAll : t≤⨆ i,C n i := by
    rw [firstChoiceCell_join_r435]
    exact inf_le_left.trans (iInf_le _ n)
  apply (le_inf le_rfl hAll).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  by_cases hi : i < b
  · exact inf_le_right.trans ((firstChoiceCell_le_r435 (V n) i).trans
      (le_iSup (fun k : {k : GroundContinuumSuccIndex // k < b} => V n k.val) ⟨i,hi⟩))
  · have hN : G b≤(W n i)ᶜ := by
      apply (iInf_le _ n).trans
      apply iSup_le
      intro a
      exact compl_le_compl (le_iSup
        (fun k : {k : GroundContinuumSuccIndex // a.val < k} => W n k.val)
        ⟨i,a.property.trans_le (le_of_not_gt hi)⟩)
    have hN' : t≤(baseEmbed Q (W n i))ᶜ :=
      (inf_le_right.trans (baseEmbed_mono_r427 Q hN)).trans_eq (baseEmbed_compl_r427 Q _)
    have hP : C n i≤baseEmbed Q (W n i) :=
      (supportProjection_le_iff_r428 Q _ _).mp le_rfl
    have hs : t⊓C n i≤⊥ := by
      have hd : Disjoint (baseEmbed Q (W n i))ᶜ (baseEmbed Q (W n i)) := disjoint_compl_left
      exact (inf_le_inf hN' hP).trans (disjoint_iff_inf_le.mp hd)
    exact hs.trans bot_le

end JSP000930.Positive
