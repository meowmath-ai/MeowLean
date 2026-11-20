import JSP000933HistoryCalibration

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion

variable {T : Type} {a : OmegaTwoIndex} {old : PrefixValidator a T}

noncomputable def goodLabelTrace (q : GoodPrefix old) : Finset (OmegaTwoIndex × T) := by
  classical
  exact (encodePrefix q).image (fun r => (r.1.1,r.2))

theorem mem_goodLabelTrace_r159 (q : GoodPrefix old) (i : OmegaTwoIndex) (x : T) :
    (i,x) ∈ goodLabelTrace q ↔ q.trace i = some x := by
  classical
  unfold goodLabelTrace
  constructor
  · intro h
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp h
    have hi : r.1.1 = i := congrArg Prod.fst he
    have hx : r.2 = x := congrArg Prod.snd he
    exact hi ▸ hx ▸ (mem_encodePrefix_r97 q r.1 r.2).mp hr
  · intro he
    let i' : ↥(Set.Iio a) := ⟨i,q.bounded i ⟨x,he⟩⟩
    exact Finset.mem_image.mpr ⟨(i',x),(mem_encodePrefix_r97 q i' x).mpr he,rfl⟩

noncomputable def goodTraceCode (E : DiamondEncoder T) (q : GoodPrefix old) : OmegaTwoIndex :=
  E.trace (goodLabelTrace q)

theorem goodTraceCode_actual_r159 [Preorder T] (policy : StagePolicy OmegaTwoIndex T)
    (E : DiamondEncoder T) (q : Before (iterationRules policy) a) :
    goodTraceCode E ((prefixOrderIso_r85 policy a) q) = E.conditionCode q.1 := by
  apply congrArg (E.trace : Finset (OmegaTwoIndex × T) → OmegaTwoIndex)
  apply Finset.ext
  rintro ⟨i,x⟩
  rw [mem_goodLabelTrace_r159,mem_labelledSupport_r117]
  rfl

noncomputable def historyDomain [Preorder T] (E : DiamondEncoder T) (G : Set OmegaTwoIndex)
    (j : OmegaTwoIndex) : RO (GoodPrefix old) :=
  ⨆ q : {q : GoodPrefix old // E.domainTag j (goodTraceCode E q) ∈ G}, imageCondition q.1

end FiniteSupport
end JSP000933
