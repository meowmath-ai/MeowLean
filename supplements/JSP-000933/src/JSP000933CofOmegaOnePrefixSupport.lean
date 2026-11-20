import JSP000933RelativeRankedRealNames
import JSP000933PreparedOmegaOneCofinalGraphs

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel MarkedForcing BooleanCompletion OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem checkedCofOmegaOne_enumerated_r488 (d : GroundContinuumSuccIndex)
    (hd : OmegaOneCofinalIndex d) :
    ∃ f : OmegaOneIndex→GroundContinuumSuccIndex,
      (∀ i,f i<d) ∧ ∀ k<d,∃ i,k<f i := by
  obtain ⟨f,hf,hC⟩ := exists_groundOmegaOne_cofinal_r423 d hd
  obtain ⟨e⟩ := Cardinal.eq.mp (mk_OmegaOneIndex_r61.trans baseOmegaOne_type_card_r391.symm)
  refine ⟨fun i => f (e i),fun i => hf (e i),fun a ha => ?_⟩
  obtain ⟨i,hi⟩ := hC a ha
  exact ⟨e.symm i,by simpa only [Equiv.apply_symm_apply] using hi⟩

theorem finiteScope_has_cofinalBound_r488 {d : GroundContinuumSuccIndex}
    (f : OmegaOneIndex→GroundContinuumSuccIndex) (hf : ∀ i,f i<d)
    (hC : ∀ k<d,∃ i,k<f i) (s : Finset GroundContinuumSuccIndex)
    (hs : ∀ k∈s,k<d) :
    ∃ j : OmegaOneIndex,∀ k∈s,k<f j := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
    intro _
    have hI : Nonempty OmegaOneIndex :=
      Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos)
    obtain ⟨i⟩ := hI
    exact ⟨i,fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | insert a s ha ih =>
    intro hs
    obtain ⟨i,hi⟩ := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    have haD : a<d := hs a (Finset.mem_insert_self _ _)
    obtain ⟨j,hj⟩ := hC (max a (f i)) (max_lt haD (hf i))
    refine ⟨j,fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk'
    · exact (le_max_left _ _).trans_lt hj
    · exact (hi k hk').trans ((le_max_right _ _).trans_lt hj)

theorem cofinalEnum_countablePrefix_bounded_r488 (d : GroundContinuumSuccIndex)
    (hd : OmegaOneCofinalIndex d) (f : OmegaOneIndex→GroundContinuumSuccIndex) (hf : ∀ i,f i<d)
    (b : OmegaOneIndex) :
    ∃ a<d,∀ i<b,f i≤a := by
  let I := ↥(Set.Iio b)
  let g (i : I) := continuumSuccOrdinal (f i.val)
  have hSm : Cardinal.mk I<(continuumSuccOrdinal d).cof := by
    change (continuumSuccOrdinal d).cof=ℵ₁ at hd
    rw [hd]
    exact (Cardinal.mk_le_aleph0_iff.mpr (OmegaOneIndex_initial_countable_r61 b)).trans_lt
      Cardinal.aleph0_lt_aleph_one
  have hO : (⨆ i,g i)<continuumSuccOrdinal d :=
    Ordinal.iSup_lt_of_lt_cof hSm (fun i => (continuumSuccIndex_lt_iff_r399 _ _).mp (hf i.val))
  let a := continuumSuccIndexOf (⨆ i,g i) (hO.trans (continuumSuccOrdinal_lt_r392 d))
  have ha : continuumSuccOrdinal a=⨆ i,g i := continuumSuccIndexOf_ordinal_r399 _ _
  refine ⟨a,(continuumSuccIndex_lt_iff_r399 _ _).mpr (ha.trans_lt hO),fun i hi => ?_⟩
  exact (continuumSuccIndex_le_iff_r399 _ _).mpr ((Ordinal.le_iSup g ⟨i,hi⟩).trans_eq ha.symm)

theorem localReal_of_cofOmegaOnePrefix_r488 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex N B)
    (d : GroundContinuumSuccIndex) (hd : OmegaOneCofinalIndex d)
    (scope : N→Finset GroundContinuumSuccIndex) (hScope : ∀ n a,a∈scope n → a<d)
    (x : ℕ→TotalBA Q) (p : TotalBA Q) (hp : p≠⊥) :
    ∃ (rank : N→OmegaOneIndex) (c b : OmegaOneIndex) (a : GroundContinuumSuccIndex)
        (m : B) (r : TotalCondition Q),
      a<d ∧ m≠⊥ ∧ imageCondition r≤p⊓baseEmbed Q m ∧
      (∀ n,rank n<b→∀ k∈scope n,k<a) ∧
      ∀ j,baseEmbed Q m⊓x j=baseEmbed Q m⊓rankedInitialGreedy Q E rank (x j) c b := by
  obtain ⟨f,hf,hC⟩ := checkedCofOmegaOne_enumerated_r488 d hd
  have hR (n : N) : ∃ j : OmegaOneIndex,∀ k∈scope n,k<f j :=
    finiteScope_has_cofinalBound_r488 f hf hC (scope n) (hScope n)
  choose rank hRank using hR
  obtain ⟨c,b,m,r,hm,hr,hEq⟩ := local_rankedRealNames_r487 Q hQ hB E rank x p hp
  obtain ⟨a,ha,hBound⟩ := cofinalEnum_countablePrefix_bounded_r488 d hd f hf b
  exact ⟨rank,c,b,a,m,r,ha,hm,hr,fun n hb k hk => (hRank n k hk).trans_le (hBound (rank n) hb),hEq⟩

end RelativeOCA
end JSP000933
