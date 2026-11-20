import JSP000933RelativeKappaNameCuts

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel MarkedForcing BooleanCompletion OpenGraphForcing

variable {B N I : Type} [CompleteBooleanAlgebra B]

open scoped Classical in
noncomputable def groundMixedEnumeration (f : I→N) (hf : Function.Surjective f) :
    MixedEnumeration I N B where
  cell i n := if f i=n then ⊤ else ⊥
  rowFull i := by
    apply top_unique
    apply le_iSup_of_le (f i)
    simp
  colFull n := by
    obtain ⟨i,hi⟩ := hf n
    apply top_unique
    apply le_iSup_of_le i
    simp [hi]
  rowApart i := by
    intro n k h
    by_cases hn : f i=n
    · simp [hn,h]
    · simp [hn]

theorem exists_groundKappaTraceEnumeration_r477 (N : Type) [Nonempty N]
    (hN : Cardinal.mk N≤GroundContinuumSucc) :
    ∃ f : GroundContinuumSuccIndex→N,Function.Surjective f := by
  classical
  obtain ⟨e⟩ := (Cardinal.le_def N GroundContinuumSuccIndex).mp
    (hN.trans_eq continuumSuccIndex_card_r406.symm)
  let alt : N := Classical.choice inferInstance
  let f (i : GroundContinuumSuccIndex) : N := if h : ∃ n,e n=i then Classical.choose h else alt
  refine ⟨f,fun n => ⟨e n,?_⟩⟩
  have he : ∃ a,e a=e n := ⟨n,rfl⟩
  apply e.injective
  simpa only [f,dite_eq_left he] using Classical.choose_spec he

abbrev WholeFiniteTrace := Finset (GroundContinuumSuccIndex×OmegaOneIndex)

theorem wholeFiniteTrace_card_r477 : Cardinal.mk WholeFiniteTrace≤GroundContinuumSucc := by
  have hK : (ℵ₀ : Cardinal)≤GroundContinuumSucc := Cardinal.aleph0_le_continuum.trans (Order.le_succ _)
  have hW : (ℵ₀ : Cardinal)≤Cardinal.mk (GroundContinuumSuccIndex×OmegaOneIndex) := by
    rw [Cardinal.mk_prod,continuumSuccIndex_card_r406,mk_OmegaOneIndex_r61]
    simp only [Cardinal.lift_id]
    exact (Cardinal.aleph0_le_mul_iff).mpr ⟨ne_of_gt (Cardinal.aleph0_pos.trans_le hK),
      ne_of_gt (Cardinal.aleph0_pos.trans_le Cardinal.isRegular_aleph_one.1),Or.inl hK⟩
  letI : Infinite (GroundContinuumSuccIndex×OmegaOneIndex) := Cardinal.infinite_iff.mpr hW
  rw [WholeFiniteTrace,Cardinal.mk_finset_of_infinite,Cardinal.mk_prod,
    continuumSuccIndex_card_r406,mk_OmegaOneIndex_r61]
  simp only [Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hK le_rfl (Cardinal.aleph_one_le_continuum.trans (Order.le_succ _))

theorem groundKappaEnumeration_prefixStages_bounded_r477
    (f : GroundContinuumSuccIndex→N) (stages : N→Finset GroundContinuumSuccIndex)
    (c : GroundContinuumSuccIndex) :
    ∃ b : GroundContinuumSuccIndex,∀ i<c,∀ a∈stages (f i),a<b := by
  classical
  let J := ↥(Set.Iio c)
  let S (j : J) := ↥(stages (f j.val))
  have hE (j : J) : Nonempty (S j↪ℕ) :=
    (Cardinal.le_def _ _).mp (by rw [Cardinal.mk_nat]; exact Cardinal.mk_le_aleph0)
  let e (j : J) := Classical.choice (hE j)
  let encode (q : Σ j,S j) : J×ℕ := (q.1,e q.1 q.2)
  have hEnc : Function.Injective encode := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have he : i=j := congrArg Prod.fst h
    subst j
    have hxy : x=y := (e i).injective (congrArg Prod.snd h)
    subst y
    rfl
  have hShort : Cardinal.mk (Σ j,S j)<GroundContinuumSucc := by
    apply (Cardinal.mk_le_of_injective hEnc).trans_lt
    rw [Cardinal.mk_prod,Cardinal.mk_nat]
    simp only [Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt groundContinuumSucc_regular_r392.1
      (continuumSuccInitial_card_lt_r406 c)
      (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _))
  obtain ⟨b,hB⟩ := continuumSuccIndex_family_bounded_r399 (fun q : Σ j,S j => q.2.val) hShort
  exact ⟨b,fun i hi a ha => hB ⟨⟨i,hi⟩,⟨a,ha⟩⟩⟩

end RelativeOCA
end JSP000933
