import JSP000933KappaPairCode

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel MarkedForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def codeTraceStageBound (f : GroundContinuumSuccIndex→N)
    (scope : N→Finset GroundContinuumSuccIndex) (i : GroundContinuumSuccIndex) :
    GroundContinuumSuccIndex :=
  Classical.choose (kappaCodeAndTrace_prefix_bound_r483 f scope i)

theorem codeTraceStageBound_spec_r484 (f : GroundContinuumSuccIndex→N)
    (scope : N→Finset GroundContinuumSuccIndex) (a : GroundContinuumSuccIndex) :
    (∀ i<a,∀ j<a,kappaPairCode (i,j)<codeTraceStageBound f scope a) ∧
      (∀ i<a,∀ k∈scope (f i),k<codeTraceStageBound f scope a) :=
  Classical.choose_spec (kappaCodeAndTrace_prefix_bound_r483 f scope a)

noncomputable def greedyNoLateCut (Q : ValuedPoset B N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f) (x : TotalBA Q)
    (b : GroundContinuumSuccIndex) : B :=
  (aboveKappaValue (greedyRowActive Q (groundMixedEnumeration f hf) x) b)ᶜ

open scoped Classical in
noncomputable def clubProbeCut (Q : ValuedPoset B N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (scope : N→Finset GroundContinuumSuccIndex) (x : GroundContinuumSuccIndex→TotalBA Q)
    (i b : GroundContinuumSuccIndex) : B :=
  if codeTraceStageBound f scope i<b then greedyNoLateCut Q f hf (x i) b else ⊥

theorem greedyNoLateCut_mono_r484 (Q : ValuedPoset B N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f) (x : TotalBA Q) :
    Monotone (greedyNoLateCut Q f hf x) := by
  intro a b hab
  apply compl_le_compl
  apply iSup_le
  intro j
  exact le_iSup (fun k : {k : GroundContinuumSuccIndex // a < k} =>
    greedyRowActive Q (groundMixedEnumeration f hf) x k.val) ⟨j.val,hab.trans_lt j.property⟩

theorem clubProbeCut_cover_r484 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsSmallKappaNames B)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (scope : N→Finset GroundContinuumSuccIndex) (x : GroundContinuumSuccIndex→TotalBA Q)
    (i : GroundContinuumSuccIndex) :
    (⨆ b,clubProbeCut Q f hf scope x i b)=⊤ := by
  classical
  let E : MixedEnumeration GroundContinuumSuccIndex N B := groundMixedEnumeration f hf
  have h0 := relativeCCC_kappaAntichain_bounded_r475 Q hQ hB (greedyTraceWeight Q E (x i))
    (greedyTraceWeight_valid_r465 Q E (x i)) (greedyTraceWeight_apart_r465 Q E (x i))
  have hTop : (⨆ b,greedyNoLateCut Q f hf (x i) b)=⊤ := by
    have h := congrArg (fun z : B => zᶜ) h0
    rw [unboundedKappaValue,compl_iInf,compl_bot] at h
    exact h
  apply top_unique
  rw [← hTop]
  apply iSup_le
  intro b
  obtain ⟨d,hd⟩ := continuumSuccIndex_family_bounded_r399
    (fun c : Bool => if c then b else codeTraceStageBound f scope i)
    (by rw [Cardinal.mk_bool]; exact (Cardinal.nat_lt_continuum 2).trans (Order.lt_succ _))
  have hb : b<d := by simpa using hd true
  have hi : codeTraceStageBound f scope i<d := by simpa using hd false
  apply le_iSup_of_le d
  rw [clubProbeCut,ite_eq_left hi]
  exact greedyNoLateCut_mono_r484 Q f hf (x i) hb.le

theorem clubProbeCut_noLate_r484 (Q : ValuedPoset B N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (scope : N→Finset GroundContinuumSuccIndex) (x : GroundContinuumSuccIndex→TotalBA Q)
    (m : B) (d i j : GroundContinuumSuccIndex)
    (hm : m ≤ mixedClosedStageValue (clubProbeCut Q f hf scope x) d)
    (hi : i<d) (hj : d≤j) :
    Disjoint m (greedyRowActive Q (groundMixedEnumeration f hf) (x i) j) := by
  classical
  apply le_compl_iff_disjoint_right.mp
  apply (hm.trans (iInf_le (fun j : ↥(Set.Iio d) => ⨆ b : ↥(Set.Iio d),
    clubProbeCut Q f hf scope x j.val b.val) ⟨i,hi⟩)).trans
  apply iSup_le
  intro b
  unfold clubProbeCut
  split
  · exact compl_le_compl (le_iSup (fun k : {k : GroundContinuumSuccIndex // b.val < k} =>
      greedyRowActive Q (groundMixedEnumeration f hf) (x i) k.val) ⟨j,b.property.trans_le hj⟩)
  · exact bot_le

theorem clubProbeCut_scopeBound_r484 (Q : ValuedPoset B N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (scope : N→Finset GroundContinuumSuccIndex) (x : GroundContinuumSuccIndex→TotalBA Q)
    (m : B) (d i : GroundContinuumSuccIndex)
    (hM : m≠⊥) (hm : m ≤ mixedClosedStageValue (clubProbeCut Q f hf scope x) d) (hi : i<d) :
    codeTraceStageBound f scope i<d := by
  classical
  by_contra hn
  apply hM
  apply le_bot_iff.mp
  apply (hm.trans (iInf_le (fun j : ↥(Set.Iio d) => ⨆ b : ↥(Set.Iio d),
    clubProbeCut Q f hf scope x j.val b.val) ⟨i,hi⟩)).trans
  apply iSup_le
  intro b
  have hNot : ¬codeTraceStageBound f scope i<b.val :=
    fun h => hn (h.trans b.property)
  simp only [clubProbeCut,ite_eq_right hNot,le_rfl]

end RelativeOCA
end JSP000933
