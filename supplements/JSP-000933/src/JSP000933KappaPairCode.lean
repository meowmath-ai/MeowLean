import JSP000933PreparedMixedSupportDiamond

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel

noncomputable def kappaPairCode :
    (GroundContinuumSuccIndex×GroundContinuumSuccIndex)↪GroundContinuumSuccIndex := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).mp
  rw [Cardinal.mk_prod,continuumSuccIndex_card_r406]
  simp only [Cardinal.lift_id]
  exact (Cardinal.mul_eq_self groundContinuumSucc_regular_r392.1).le

theorem kappaPairCode_initial_bound_r483 (a : GroundContinuumSuccIndex) :
    ∃ b : GroundContinuumSuccIndex,∀ i<a,∀ j<a,kappaPairCode (i,j)<b := by
  let I := ↥(Set.Iio a)
  have hI : Cardinal.mk (I×I)<GroundContinuumSucc := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt groundContinuumSucc_regular_r392.1
      (continuumSuccInitial_card_lt_r406 a) (continuumSuccInitial_card_lt_r406 a)
  obtain ⟨b,hb⟩ := continuumSuccIndex_family_bounded_r399
    (fun q : I×I => kappaPairCode (q.1.val,q.2.val)) hI
  exact ⟨b,fun i hi j hj => hb (⟨i,hi⟩,⟨j,hj⟩)⟩

theorem kappaCodeAndTrace_prefix_bound_r483 {N : Type}
    (f : GroundContinuumSuccIndex→N) (scope : N→Finset GroundContinuumSuccIndex)
    (a : GroundContinuumSuccIndex) :
    ∃ b : GroundContinuumSuccIndex,
      (∀ i<a,∀ j<a,kappaPairCode (i,j)<b) ∧
      (∀ i<a,∀ k∈scope (f i),k<b) := by
  obtain ⟨b,hB⟩ := kappaPairCode_initial_bound_r483 a
  obtain ⟨d,hD⟩ := groundKappaEnumeration_prefixStages_bounded_r477 f scope a
  exact ⟨max b d,fun i hi j hj => (hB i hi j hj).trans_le (le_max_left _ _),
    fun i hi k hk => (hD i hi k hk).trans_le (le_max_right _ _)⟩

theorem omegaOneCofinalIndex_between_r483 {d a : GroundContinuumSuccIndex}
    (hd : OmegaOneCofinalIndex d) (ha : a<d) :
    ∃ b : GroundContinuumSuccIndex,a<b ∧ b<d := by
  have hLim : Order.IsSuccLimit (continuumSuccOrdinal d) := by
    apply Ordinal.one_lt_cof_iff.mp
    change (continuumSuccOrdinal d).cof=ℵ₁ at hd
    rw [hd]
    exact Cardinal.one_lt_aleph0.trans Cardinal.aleph0_lt_aleph_one
  have hLT : continuumSuccOrdinal a+1<continuumSuccOrdinal d :=
    hLim.add_one_lt ((continuumSuccIndex_lt_iff_r399 _ _).mp ha)
  let b := continuumSuccIndexOf (continuumSuccOrdinal a+1) (hLT.trans (continuumSuccOrdinal_lt_r392 d))
  have hb : continuumSuccOrdinal b=continuumSuccOrdinal a+1 := continuumSuccIndexOf_ordinal_r399 _ _
  refine ⟨b,(continuumSuccIndex_lt_iff_r399 _ _).mpr ?_,(continuumSuccIndex_lt_iff_r399 _ _).mpr ?_⟩
  · rw [hb]
    exact Order.lt_add_one_iff.mpr le_rfl
  · rw [hb]
    exact hLT

open scoped Classical in
noncomputable def packedKappaMatrix {B : Type} [CompleteBooleanAlgebra B]
    (a : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B) (i : GroundContinuumSuccIndex) : B :=
  if h : ∃ p,kappaPairCode p=i then a (Classical.choose h).1 (Classical.choose h).2 else ⊥

theorem packedKappaMatrix_eval_r483 {B : Type} [CompleteBooleanAlgebra B]
    (a : GroundContinuumSuccIndex→GroundContinuumSuccIndex→B) (i j : GroundContinuumSuccIndex) :
    packedKappaMatrix a (kappaPairCode (i,j))=a i j := by
  classical
  have h : ∃ p,kappaPairCode p=kappaPairCode (i,j) := ⟨(i,j),rfl⟩
  have he : Classical.choose h=(i,j) := kappaPairCode.injective (Classical.choose_spec h)
  simp only [packedKappaMatrix,dite_eq_left h,he]

end RelativeOCA
end JSP000933
