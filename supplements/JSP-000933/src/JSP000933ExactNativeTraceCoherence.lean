import JSP000933RawTailCCCAndTraceJoins

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion MarkedForcing FiniteSupport RelativeOCA OpenGraphForcing

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

noncomputable def includeRawTail {f g : A→Prop} (h : ∀ i, f i → g i) (n : RawTail T f) :
    RawTail T g :=
  ⟨n.trace,n.finite,fun i hi => h i (n.bounded i hi)⟩

theorem native_bounded_of_stripped {tail : BasedTailPolicy A B T} (p : BasedCondition tail)
    {a : A} (ha : (⊥ : A)<a) (n : PrefixTail a T)
    (hs : stripBaseTrace p.trace=n.trace) :
    ∀ i, present p.trace i → i<a := by
  intro i h
  by_cases hi : i=⊥
  · exact hi.symm ▸ ha
  · obtain ⟨s,hs'⟩ := h
    apply n.bounded i
    refine ⟨s.2,?_⟩
    rw [←hs]
    simp [stripBaseTrace,hi,hs']

theorem prefix_to_whole_traceValue (tail : BasedTailPolicy A B T) {a : A}
    (ha : (⊥ : A)<a) (n : PrefixTail a T) :
    (wholeReduction (R := iterationRules (basedPolicy tail)) a).boolPullback
      ((prefixTailPresentation tail ha).denseMap.pullIso
        (traceValue (prefixTailPresentation tail ha).quotient n)) =
      (wholeTailPresentation tail).denseMap.pullIso
        (traceValue (wholeTailPresentation tail).quotient
          (includeRawTail (fun _ _ => trivial) n)) := by
  rw [(prefixTailPresentation tail ha).pull_tail_traceValue,
    (wholeTailPresentation tail).pull_tail_traceValue]
  rw [RestrictionMap.boolPullback_iSup_r91]
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [wholeReduction_basic_r100]
    have hp : (wholeTailPresentation tail).strip p.val.val =
        includeRawTail (fun _ _ => trivial) n := RawTail.extTrace (congrArg (fun r : PrefixTail a T => r.trace) p.property)
    exact le_iSup (fun r : {r : BasedCondition tail // (wholeTailPresentation tail).strip r =
      includeRawTail (fun _ _ => trivial) n} => imageCondition r.val) ⟨p.val.val,hp⟩
  · apply iSup_le
    intro p
    have hs : stripBaseTrace p.val.trace = n.trace := congrArg (fun r : WholeTail A T => r.trace) p.property
    let q : BasedBefore tail a := ⟨p.val,native_bounded_of_stripped p.val ha n hs⟩
    have hq : (prefixTailPresentation tail ha).strip q=n := RawTail.extTrace hs
    apply le_iSup_of_le (⟨q,hq⟩ : {p : BasedBefore tail a //
      (prefixTailPresentation tail ha).strip p=n})
    rw [wholeReduction_basic_r100]

theorem earlier_to_later_traceValue (tail : BasedTailPolicy A B T) {a d : A}
    (ha : (⊥ : A)<a) (had : a≤d) (n : PrefixTail a T) :
    (prefixReduction (R := iterationRules (basedPolicy tail)) had).boolPullback
      ((prefixTailPresentation tail ha).denseMap.pullIso
        (traceValue (prefixTailPresentation tail ha).quotient n)) =
      (prefixTailPresentation tail (ha.trans_le had)).denseMap.pullIso
        (traceValue (prefixTailPresentation tail (ha.trans_le had)).quotient
          (includeRawTail (fun _ h => h.trans_le had) n)) := by
  rw [(prefixTailPresentation tail ha).pull_tail_traceValue,
    (prefixTailPresentation tail (ha.trans_le had)).pull_tail_traceValue]
  rw [RestrictionMap.boolPullback_iSup_r91]
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [prefixReduction_basic_r92]
    have hp : (prefixTailPresentation tail (ha.trans_le had)).strip (includeBefore had p.val) =
        includeRawTail (fun _ h => h.trans_le had) n :=
      RawTail.extTrace (congrArg (fun r : PrefixTail a T => r.trace) p.property)
    exact le_iSup (fun r : {r : BasedBefore tail d // (prefixTailPresentation tail (ha.trans_le had)).strip r =
      includeRawTail (fun _ h => h.trans_le had) n} => imageCondition r.val) ⟨includeBefore had p.val,hp⟩
  · apply iSup_le
    intro p
    have hs : stripBaseTrace p.val.val.trace = n.trace := congrArg (fun r : PrefixTail d T => r.trace) p.property
    let q : BasedBefore tail a := ⟨p.val.val,native_bounded_of_stripped p.val.val ha n hs⟩
    have hq : (prefixTailPresentation tail ha).strip q=n := RawTail.extTrace hs
    apply le_iSup_of_le (⟨q,hq⟩ : {p : BasedBefore tail a //
      (prefixTailPresentation tail ha).strip p=n})
    rw [prefixReduction_basic_r92]
    exact le_rfl

end ForcingTransport
end JSP000933
