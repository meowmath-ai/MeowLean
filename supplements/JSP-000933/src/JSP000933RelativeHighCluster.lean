import JSP000933RelativeExceptionalTuples
import JSP000933RelativeMixedCluster

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem exists_relativeHighCluster_r458 (hB : BoundsCountableOmegaOneNames B)
    (D : (ℕ→B)→B) (K : Word×Word→B) (m : B)
    (Y : OmegaOneIndex→ℕ→B) (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    {n : ℕ}
    (lower : CardRelativeCCC m (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) n)
    (a : LabelCandidate→Fin (n+1)→OmegaOneIndex)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (hW : unboundedValue (rowLabelWeight W)≠⊥)
    (hOwn : ∀ i s,W i s≤cliqueAdmitted m (fun i => D (Y i))
      (fun i j => colorValue K (Y i) (Y j)) s)
    (hMono : ∀ i s,W i s≠⊥ → StrictMono (a (i,s)))
    (hMem : ∀ i s,W i s≠⊥ → ∀ j,a (i,s) j∈s)
    (hDis : ∀ i j,i<j→∀ s t,¬Disjoint s t → Disjoint (W i s) (W j t)) :
    ∃ (f : ℕ→BooleanSample B n) (code : OmegaOneIndex) (x : LabelCandidate) (q : B),
      q≠⊥ ∧ q≤W x.1 x.2 ∧ code<a x (Fin.last n) ∧
      q≤tableAgreement (sampleTable f) (sampleTable ((relativeScheduleFromEnum e).sampleCode n code)) ∧
      q≤weightedCluster K (labelSamples Y a W)
        ((labelSamples Y a W x).stem) ((labelSamples Y a W x).tip) ∧
      ∀ stem z,weightedCluster K (labelSamples Y a W) stem z=weightedCluster K f stem z := by
  classical
  let F := labelSamples Y a W
  obtain ⟨f,hF⟩ := exists_mixedClusterSequence_r452 K F
  let T (c : OmegaOneIndex) :=
    tableAgreement (sampleTable f) (sampleTable ((relativeScheduleFromEnum e).sampleCode n c))
  have hTop : (⨆ c,T c)=⊤ := relativeSampleCodes_cover_r441 e hE f
  let u := unboundedValue (rowLabelWeight W)
  have hTotal : u≤⨆ c,T c := hTop.symm ▸ le_top
  obtain ⟨code,p,hp,hpu,hpt⟩ := exists_nonzero_below_choice_r135 u hW T hTotal
  let last (x : LabelCandidate) := a x (Fin.last n)
  have hLast (i j : OmegaOneIndex) (hij : i<j) (s t : Finset OmegaOneIndex)
      (h : last (i,s)=last (j,t)) : Disjoint (W i s) (W j t) := by
    by_cases hs : W i s=⊥
    · rw [hs]
      exact disjoint_bot_left
    by_cases ht : W j t=⊥
    · rw [ht]
      exact disjoint_bot_right
    apply hDis i j hij s t
    intro hd
    change a (i,s) (Fin.last n) = a (j,t) (Fin.last n) at h
    exact (Finset.disjoint_left.mp hd (hMem i s hs (Fin.last n)))
      (h.symm ▸ hMem j t ht (Fin.last n))
  let High := restrictLabels W (fun x => code<last x)
  let V (i : OmegaOneIndex) (s : Finset OmegaOneIndex) := p⊓High i s
  have hU : unboundedValue (rowLabelWeight V)=p := by
    rw [rowLabelWeight_meetConst_r456,unboundedValue_meetConst_r456]
    change p⊓unboundedValue (rowLabelWeight (restrictLabels W (fun x => code<last x)))=p
    rw [highLast_keepsUnbounded_r454 hB W last hLast code]
    exact inf_eq_left.mpr hpu
  have hSub (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : V i s≤W i s := by
    unfold V High restrictLabels
    split
    · exact inf_le_right
    · simp only [inf_bot_eq,bot_le]
  have hSome : ∃ x : LabelCandidate,
      V x.1 x.2⊓weightedCluster K F (F x).stem (F x).tip≠⊥ := by
    by_contra hn
    have hFail (i : OmegaOneIndex) (s : Finset OmegaOneIndex) :
        V i s⊓weightedCluster K F (F (i,s)).stem (F (i,s)).tip=⊥ := by
      by_contra hh
      exact hn ⟨(i,s),hh⟩
    have h0 := relativeExceptional_bounded_r457 hB D K m Y lower a W V hSub hOwn hMono hMem hDis hFail
    exact hp (hU.symm.trans h0)
  obtain ⟨x,hx⟩ := hSome
  let q := V x.1 x.2⊓weightedCluster K F (F x).stem (F x).tip
  have hxAbove : code<last x := by
    by_contra hn
    apply hx
    change (p⊓restrictLabels W (fun x => code<last x) x.1 x.2)⊓_ =⊥
    have hPair : (x.1,x.2)=x := rfl
    simp only [restrictLabels,hPair,ite_eq_right hn,inf_bot_eq,bot_inf_eq]
  exact ⟨f,code,x,q,hx,inf_le_left.trans (hSub x.1 x.2),hxAbove,
    inf_le_left.trans (inf_le_left.trans hpt),inf_le_right,hF⟩

end RelativeOCA
end JSP000933
