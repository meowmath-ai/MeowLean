import JSP000933RelativeSmallQuotientCH

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def traceRanksBelow (E : MixedEnumeration OmegaOneIndex N B)
    (rank : N→OmegaOneIndex) (i b : OmegaOneIndex) : B :=
  ⨆ n : {n : N // rank n<b},E.cell i n.val

theorem traceRanksBelow_mono_r486 (E : MixedEnumeration OmegaOneIndex N B)
    (rank : N→OmegaOneIndex) (i : OmegaOneIndex) : Monotone (traceRanksBelow E rank i) := by
  intro a b hab
  apply iSup_le
  intro n
  exact le_iSup (fun k : {k : N // rank k < b} => E.cell i k.val) ⟨n.val,n.property.trans_le hab⟩

theorem traceRanksBelow_cover_r486 (E : MixedEnumeration OmegaOneIndex N B)
    (rank : N→OmegaOneIndex) (i : OmegaOneIndex) :
    (⨆ b,traceRanksBelow E rank i b)=⊤ := by
  apply top_unique
  rw [← E.rowFull i]
  apply iSup_le
  intro n
  obtain ⟨b,hb⟩ := OmegaOneIndex_countable_bounded_r61 {rank n} (Set.countable_singleton _)
  exact le_iSup_of_le b (le_iSup (fun k : {k : N // rank k < b} => E.cell i k.val) ⟨n,hb _ (Set.mem_singleton _)⟩)

noncomputable def allTraceRanksBelow (E : MixedEnumeration OmegaOneIndex N B)
    (rank : N→OmegaOneIndex) (c b : OmegaOneIndex) : B :=
  ⨅ i : ↥(Set.Iio c),traceRanksBelow E rank i.val b

theorem allTraceRanksBelow_cover_r486 (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex N B) (rank : N→OmegaOneIndex) (c : OmegaOneIndex) :
    (⨆ b,allTraceRanksBelow E rank c b)=⊤ := by
  letI : Countable (↥(Set.Iio c)) := OmegaOneIndex_initial_countable_r61 c
  apply top_unique
  exact uniform_countable_cutoffs_r444 hB ⊤
    (fun i : ↥(Set.Iio c) => traceRanksBelow E rank i.val)
    (fun i => traceRanksBelow_mono_r486 E rank i.val)
    (fun i => (traceRanksBelow_cover_r486 E rank i.val).ge)

theorem allTraceRanksBelow_disjoint_r486 (E : MixedEnumeration OmegaOneIndex N B)
    (rank : N→OmegaOneIndex) (c b i : OmegaOneIndex) (hi : i<c)
    (n : N) (hn : b≤rank n) :
    Disjoint (allTraceRanksBelow E rank c b) (E.cell i n) := by
  change Disjoint (⨅ j : ↥(Set.Iio c),traceRanksBelow E rank j.val b) (E.cell i n)
  apply Disjoint.mono_left (iInf_le _ (⟨i,hi⟩ : ↥(Set.Iio c)))
  apply disjoint_iff_inf_le.mpr
  rw [traceRanksBelow,iSup_inf_eq]
  apply iSup_le
  intro j
  have he : j.val≠n := fun h => not_lt_of_ge hn (by simpa only [h] using j.property)
  exact disjoint_iff_inf_le.mp (E.rowApart i he)

end RelativeOCA
end JSP000933
