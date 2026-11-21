import JSP000930PositiveSupportedRectangles
import JSP000933LocalKappaTraceSupport
import JSP000933PreparedPrefixCHRealCodes
import JSP000933BooleanRealEquality

namespace JSP000930.Positive.Cohen

open Cardinal JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.PreparedModel JSP000933.ForcingTransport JSP000933.CantorCodes

noncomputable def bulkTraceScope (p : Trace WetzelCoordinate) : Finset GroundContinuumSuccIndex := by
  classical
  let raw := p.1.dom.image (fun x => Sum.elim some (fun _ => none) x.1)
  exact raw.filterMap id (by intro _ _ _ h₁ h₂; exact h₁.trans h₂.symm)

theorem certified_bulk_support (p : Trace WetzelCoordinate) (a : GroundContinuumSuccIndex)
    (h : ∀ i ∈ bulkTraceScope p, i < a) : Supported p (bulkPrefix a) := by
  rintro ⟨i,n⟩ hi
  cases i with
  | inl j =>
      change j < a
      apply h j
      classical
      unfold bulkTraceScope
      exact (Finset.mem_filterMap id).mpr
        ⟨some j,Finset.mem_image.mpr ⟨(Sum.inl j,n),hi,rfl⟩,rfl⟩
  | inr j => exact True.intro

theorem wetzel_real_local_bulk (x : ℕ → WetzelCohenBA) (p : WetzelCohenBA) (hp : p ≠ ⊥) :
    ∃ (a : GroundContinuumSuccIndex) (r : TotalCondition wetzelCohenPoset)
      (y : ℕ → TotalBA (valuedBlock PreparedBA (bulkPrefix a))),
      imageCondition r ≤ p ∧
      imageCondition r ≤ realEqValue x
        (fun n => (markedBlockIntoFull (bulkPrefix a)).toFun (y n)) := by
  classical
  obtain ⟨t,ht⟩ := imageCondition_dense_r50 p hp
  obtain ⟨f,hf⟩ := wetzelTraces_enumerate
  have hCCC : ForcesRelativeCCC wetzelCohenPoset :=
    cohen_forcesRelativeCCC prepared_boundsOmegaOne_r432
  have hSmall : Cardinal.mk ℕ < GroundContinuumSucc := by
    rw [Cardinal.mk_nat]
    exact Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _)
  obtain ⟨c,a,b,hb,hbt,hScope,hEq⟩ := locally_boundedGroundTraceNames_r478
    wetzelCohenPoset hCCC actual_prepared_boundsSmallKappa_r473 f hf bulkTraceScope x hSmall
      t.mask t.nonzero
  let earlier (j : ↥(Set.Iio c)) : BlockTrace (bulkPrefix a) :=
    ⟨f j.val,certified_bulk_support (f j.val) a (hScope j.val j.property)⟩
  let y (n : ℕ) : TotalBA (valuedBlock PreparedBA (bulkPrefix a)) :=
    ⨆ j : ↥(Set.Iio c),traceRectangle (valuedBlock PreparedBA (bulkPrefix a)) (earlier j)
      (greedyTraceWeight wetzelCohenPoset (groundMixedEnumeration f hf) (x n) j.val (f j.val))
  let r : TotalCondition wetzelCohenPoset := ⟨b,t.trace,hb,le_top⟩
  have hr : r ≤ t := (cohen_total_le_iff _ _).mpr ⟨hbt,le_rfl⟩
  refine ⟨a,r,y,(imageCondition_mono_r50 hr).trans ht,?_⟩
  have hReal : baseEmbed wetzelCohenPoset b ≤ realEqValue x
      (fun n => (markedBlockIntoFull (bulkPrefix a)).toFun (y n)) := by
    apply (le_realEqValue_iff_r126 _ _ _).mpr
    intro n
    have h := hEq n
    simpa only [y,(markedBlockIntoFull (bulkPrefix a)).map_iSup, markedBlock_rectangle,
      earlier] using h
  exact (image_le_baseEmbed_r427 r b le_rfl).trans hReal

end JSP000930.Positive.Cohen
