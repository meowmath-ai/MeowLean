import JSP000933ActualReflectedProbes

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel

variable {B : Type} [CompleteBooleanAlgebra B]

open scoped Classical in
noncomputable def extraStageCut (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B)
    (extra : GroundContinuumSuccIndex→GroundContinuumSuccIndex)
    (i b : GroundContinuumSuccIndex) : B := if extra i<b then F i b else ⊥

theorem extraStageCut_le_r492 (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B)
    (extra : GroundContinuumSuccIndex→GroundContinuumSuccIndex)
    (i b : GroundContinuumSuccIndex) : extraStageCut F extra i b≤F i b := by
  classical
  unfold extraStageCut
  split
  · exact le_rfl
  · exact bot_le

theorem mixedClosedStage_mono_r492 (F G : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B)
    (h : ∀ i b,F i b≤G i b) (d : GroundContinuumSuccIndex) :
    mixedClosedStageValue F d ≤ mixedClosedStageValue G d := by
  unfold mixedClosedStageValue
  apply le_iInf
  intro i
  apply (iInf_le _ i).trans
  apply iSup_le
  intro b
  exact le_iSup_of_le b (h i.val b.val)

theorem extraStageCut_cover_r492 (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B)
    (extra : GroundContinuumSuccIndex→GroundContinuumSuccIndex)
    (i : GroundContinuumSuccIndex) (hm : Monotone (F i)) (hF : (⨆ b,F i b)=⊤) :
    (⨆ b,extraStageCut F extra i b)=⊤ := by
  classical
  apply top_unique
  rw [← hF]
  apply iSup_le
  intro b
  obtain ⟨d,hd⟩ := continuumSuccIndex_family_bounded_r399 (fun x : Bool => if x then b else extra i)
    (by rw [Cardinal.mk_bool]; exact (Cardinal.nat_lt_continuum 2).trans (Order.lt_succ _))
  have hb : b<d := by simpa using hd true
  have hi : extra i<d := by simpa using hd false
  apply le_iSup_of_le d
  rw [extraStageCut,ite_eq_left hi]
  exact hm hb.le

theorem extraStageCut_absorbed_r492 (F : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B)
    (extra : GroundContinuumSuccIndex→GroundContinuumSuccIndex)
    {m : B} {d i : GroundContinuumSuccIndex}
    (hn : m≠⊥) (h : m ≤ mixedClosedStageValue (extraStageCut F extra) d) (hi : i<d) :
    extra i<d := by
  classical
  by_contra hN
  apply hn
  apply le_bot_iff.mp
  apply (h.trans (iInf_le (fun j : ↥(Set.Iio d) => ⨆ b : ↥(Set.Iio d),
    extraStageCut F extra j.val b.val) ⟨i,hi⟩)).trans
  apply iSup_le
  intro b
  have hNo : ¬extra i<b.val := fun hb => hN (hb.trans b.property)
  simp only [extraStageCut,ite_eq_right hNo,le_rfl]

theorem clubProbeCut_mono_r492 {N : Type} (Q : MarkedForcing.ValuedPoset B N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (scope : N→Finset GroundContinuumSuccIndex) (x : GroundContinuumSuccIndex→MarkedForcing.TotalBA Q)
    (i : GroundContinuumSuccIndex) : Monotone (clubProbeCut Q f hf scope x i) := by
  classical
  intro a b hab
  by_cases ha : codeTraceStageBound f scope i<a
  · simpa only [clubProbeCut,ite_eq_left ha,ite_eq_left (ha.trans_le hab)] using
      greedyNoLateCut_mono_r484 Q f hf (x i) hab
  · rw [clubProbeCut,ite_eq_right ha]
    exact bot_le

end RelativeOCA
end JSP000933
