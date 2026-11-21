import JSP000930ActualAugmentedTraceInclusion

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing

noncomputable def symbolicLabelSiteSupport {a : GroundContinuumSuccIndex}
    (p : SupportedSymbolic GroundContinuumSuccIndex (WorkingDomain a)) : Finset GroundContinuumSuccIndex := by
  classical
  exact p.val.elim ∅ (fun t => (t.pins.map Prod.fst).toFinset)

theorem symbolicLabelSiteSupport_lt {a : GroundContinuumSuccIndex}
    (p : SupportedSymbolic GroundContinuumSuccIndex (WorkingDomain a)) :
    ∀ j∈symbolicLabelSiteSupport p,j<a := by
  classical
  rcases p with ⟨p,hp⟩
  cases p with
  | none =>
    simp [symbolicLabelSiteSupport]
  | some p =>
    intro j hj
    exact hp j (List.mem_toFinset.mp hj)

noncomputable def augmentedFullSupport {a : GroundContinuumSuccIndex}
    (s : Finset GroundContinuumSuccIndex) (p : ActualAugmentedLabel a s) :
    Finset GroundContinuumSuccIndex := by
  classical
  exact wetzelScope (includeRawTail (fun _ _ => trivial) p.1) ∪
    s.attach.biUnion (fun i => symbolicLabelSiteSupport (p.2 i))

theorem augmentedFullSupport_lt {a : GroundContinuumSuccIndex} (s : Finset GroundContinuumSuccIndex)
    (p : ActualAugmentedLabel a s) :
    ∀ j∈augmentedFullSupport s p,j<a := by
  classical
  intro j hj
  rcases Finset.mem_union.mp hj with h|h
  · obtain ⟨u,hu,he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp h)
    have ht : present p.1.trace u :=
      (RawTail.mem_scope (includeRawTail (fun _ _ => trivial) p.1) u).mp (Finset.mem_toList.mp hu)
    cases u with
    | none => cases he
    | some u =>
      cases u with
      | bot => cases he
      | coe u =>
        change some u = some j at he
        have he' : u=j := Option.some.inj he
        subst j
        exact (wetzelWorkStage_lt_iff _ _).mp (p.1.bounded (wetzelWorkStage u) ht)
  · obtain ⟨i,_,hj⟩ := Finset.mem_biUnion.mp h
    exact symbolicLabelSiteSupport_lt (p.2 i) j hj

theorem actualAugmentedLabels_exist_at_cut {a b : GroundContinuumSuccIndex} (h : b≤a)
    (s : Finset GroundContinuumSuccIndex) (p : ActualAugmentedLabel a s)
    (hp : ∀ j∈augmentedFullSupport s p,j<b) :
    ∃ q : ActualAugmentedLabel b s,actualAugmentedIncludeLabel h s q = p := by
  classical
  let t := includeRawTail (fun _ _ => trivial) p.1
  have hRaw : TraceBelow wetzelScope b t :=
    fun j hj => hp j (Finset.mem_union_left _ hj)
  let u : NativeWetzelTrace b := wetzelEarlierTrace b t hRaw
  have hPins (i : s) : SymbolicLabelAt (WorkingDomain b) (p.2 i).val := by
    cases he : (p.2 i).val with
    | none => exact True.intro
    | some q =>
      intro j hj
      have hM : j∈symbolicLabelSiteSupport (p.2 i) := by
        simp only [symbolicLabelSiteSupport,he,Option.elim_some,List.mem_toFinset]
        exact hj
      exact hp j (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_attach _ _,hM⟩))
  let v : ActualSurvivorLabels b s := fun i => ⟨(p.2 i).val,hPins i⟩
  refine ⟨(u,v),?_⟩
  apply Prod.ext
  · exact RawTail.extTrace rfl
  · funext i
    exact Subtype.ext rfl

theorem actualAugmentedBasis_earlier {a : GroundContinuumSuccIndex} (hL : CheckedGroundLimit a)
    (s : Finset GroundContinuumSuccIndex) (p : ActualAugmentedLabel a s) :
    ∃ (b : GroundContinuumSuccIndex) (h : b<a) (q : ActualAugmentedLabel b s),
      actualAugmentedIncludeLabel h.le s q = p := by
  obtain ⟨b,hb,hP⟩ := checkedCut_contains_finset hL.1 hL.2
    (augmentedFullSupport s p) (augmentedFullSupport_lt s p)
  obtain ⟨q,hq⟩ := actualAugmentedLabels_exist_at_cut hb.le s p hP
  exact ⟨b,hb,q,hq⟩

end JSP000930.Negative
