import JSP000933RawTailCardinality
import JSP000933GroundKappaTraceEnum
import Mathlib.Logic.Equiv.Option

open Cardinal

namespace JSP000933
namespace ForcingTransport

open FiniteSupport PreparedModel OpenGraphForcing

abbrev OCARawStage := WithBot GroundContinuumSuccIndex
abbrev OCARawLabel := Finset OmegaOneIndex
abbrev OCAWholeRawTail := WholeTail OCARawStage OCARawLabel
abbrev OCAPrefixRawTail (a : GroundContinuumSuccIndex) :=
  PrefixTail (a : OCARawStage) OCARawLabel

private theorem option_card_le_r491 (I : Type) {c : Cardinal}
    (hc : ℵ₀≤c) (hI : Cardinal.mk I≤c) : Cardinal.mk (Option I)≤c := by
  rw [Cardinal.mk_option]
  exact Cardinal.add_le_of_le hc hI (Cardinal.one_lt_aleph0.le.trans hc)

private theorem label_card_r491 : Cardinal.mk OCARawLabel=ℵ₁ := by
  letI : Infinite OmegaOneIndex := Cardinal.infinite_iff.mpr
    (by rw [mk_OmegaOneIndex_r61]; exact Cardinal.aleph0_lt_aleph_one.le)
  exact (Cardinal.mk_finset_of_infinite _).trans mk_OmegaOneIndex_r61

theorem wholeRawTail_card_r491 : Cardinal.mk OCAWholeRawTail≤GroundContinuumSucc := by
  have hC : (ℵ₀ : Cardinal)≤GroundContinuumSucc :=
    Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  have hO : Cardinal.mk OCARawStage≤GroundContinuumSucc := by
    change Cardinal.mk (Option GroundContinuumSuccIndex)≤GroundContinuumSucc
    exact option_card_le_r491 _ hC continuumSuccIndex_card_r406.le
  apply RawTail.card_le_r490 hC
  · have hI : Function.Injective
        (Subtype.val : {i : OCARawStage // True}→OCARawStage) := Subtype.val_injective
    exact (Cardinal.mk_le_of_injective hI).trans hO
  · rw [label_card_r491]
    exact Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)

private def prefixCoordinateCode_r491 (a : GroundContinuumSuccIndex)
    (x : {i : OCARawStage // i<(a : OCARawStage)}) :
    Option (↥(Set.Iio a)) := by
  obtain ⟨i,hi⟩ := x
  cases i with
  | none => exact none
  | some j => exact some ⟨j,WithBot.coe_lt_coe.mp hi⟩

private theorem prefixCoordinateCode_injective_r491 (a : GroundContinuumSuccIndex) :
    Function.Injective (prefixCoordinateCode_r491 a) := by
  have hM (x : {i : OCARawStage // i<(a : OCARawStage)}) :
      (prefixCoordinateCode_r491 a x).map Subtype.val =
        (show Option GroundContinuumSuccIndex from x.val) := by
    obtain ⟨i,hi⟩ := x
    cases i <;> rfl
  intro x y h
  apply Subtype.ext
  exact (hM x).symm.trans ((congrArg (Option.map Subtype.val) h).trans (hM y))

theorem prefixRawTail_card_r491 (a : GroundContinuumSuccIndex) :
    Cardinal.mk (OCAPrefixRawTail a)≤𝔠 := by
  apply RawTail.card_le_r490 Cardinal.aleph0_le_continuum
  · apply (Cardinal.mk_le_of_injective (prefixCoordinateCode_injective_r491 a)).trans
    exact option_card_le_r491 _ Cardinal.aleph0_le_continuum
      (Order.lt_succ_iff.mp (continuumSuccInitial_card_lt_r406 a))
  · rw [label_card_r491]
    exact Cardinal.aleph_one_le_continuum

noncomputable def physicalRawTailScope_r491 {allowed : OCARawStage→Prop}
    (r : RawTail OCARawLabel allowed) : Finset GroundContinuumSuccIndex :=
  r.scope.filterMap (fun i => (show Option GroundContinuumSuccIndex from i))
    (by intro _ _ _ h₁ h₂; exact h₁.trans h₂.symm)

theorem mem_physicalRawTailScope_r491 {allowed : OCARawStage→Prop}
    (r : RawTail OCARawLabel allowed) (a : GroundContinuumSuccIndex) :
    a∈physicalRawTailScope_r491 r ↔ present r.trace (a : OCARawStage) := by
  have hMem : a∈physicalRawTailScope_r491 r ↔
      ∃ i ∈ r.scope, (show Option GroundContinuumSuccIndex from i) = some a := by
    unfold physicalRawTailScope_r491
    exact @Finset.mem_filterMap OCARawStage GroundContinuumSuccIndex _ r.scope _ a
  constructor
  · intro h
    obtain ⟨i,hi,he⟩ := hMem.mp h
    have hie : i=(a : OCARawStage) := he
    exact (RawTail.mem_scope _ _).mp (hie ▸ hi)
  · intro h
    exact hMem.mpr ⟨(a : OCARawStage),(RawTail.mem_scope _ _).mpr h,rfl⟩

theorem physicalRawTailScope_lt_iff_r491 {allowed : OCARawStage→Prop}
    (r : RawTail OCARawLabel allowed) (a : GroundContinuumSuccIndex) :
    (∀ k∈physicalRawTailScope_r491 r,k<a) ↔
      ∀ i,present r.trace i → i<(a : OCARawStage) := by
  constructor
  · intro h i hi
    cases i with
    | none => exact WithBot.bot_lt_coe a
    | some k => exact WithBot.coe_lt_coe.mpr (h k ((mem_physicalRawTailScope_r491 _ _).mpr hi))
  · intro h k hk
    exact WithBot.coe_lt_coe.mp (h _ ((mem_physicalRawTailScope_r491 _ _).mp hk))

theorem prefixRawTail_physicalScope_r491 (a : GroundContinuumSuccIndex)
    (r : OCAPrefixRawTail a) : ∀ k∈physicalRawTailScope_r491 r,k<a :=
  (physicalRawTailScope_lt_iff_r491 r a).mpr r.bounded

end ForcingTransport
end JSP000933
