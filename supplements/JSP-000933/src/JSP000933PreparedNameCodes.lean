import JSP000933PreparedCutDecisions

open Cardinal

namespace JSP000933
namespace PreparedModel

theorem continuumSuccIndex_card_r406 : Cardinal.mk GroundContinuumSuccIndex=GroundContinuumSucc := by
  change Cardinal.mk GroundContinuumSucc.ord.ToType=GroundContinuumSucc
  rw [Cardinal.mk_toType,Cardinal.card_ord]

theorem continuumSuccInitial_card_lt_r406 (b : GroundContinuumSuccIndex) :
    Cardinal.mk (↥(Set.Iio b))<GroundContinuumSucc := by
  let f (a : ↥(Set.Iio b)) : (continuumSuccOrdinal b).ToType :=
    Ordinal.ToType.mk ⟨continuumSuccOrdinal a.val,
      (continuumSuccIndex_lt_iff_r399 _ _).mp a.property⟩
  have hF : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply continuumSuccIndex_injective_r399
    exact congrArg (fun z : Set.Iio (continuumSuccOrdinal b) => z.val)
      ((Ordinal.ToType.mk (o := continuumSuccOrdinal b)).injective he)
  have hCard : Cardinal.mk (continuumSuccOrdinal b).ToType<GroundContinuumSucc := by
    rw [Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp (continuumSuccOrdinal_lt_r392 b)
  exact (Cardinal.mk_le_of_injective hF).trans_lt hCard

noncomputable def collapseNameCode :
    (CollapseBasicCondition×GroundContinuumSuccIndex)↪GroundContinuumSuccIndex := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).mp
  rw [Cardinal.mk_prod,continuumSuccIndex_card_r406]
  simp only [Cardinal.lift_id]
  exact Cardinal.mul_le_of_le groundContinuumSucc_regular_r392.1
    (basicValue_card_le_continuum_r401.trans (Order.le_succ _)) le_rfl

theorem collapseNameCode_bounded_r406 (b : GroundContinuumSuccIndex) :
    ∃ c : GroundContinuumSuccIndex,∀ p : CollapseBasicCondition,∀ i<b,
      collapseNameCode (p,i)<c := by
  let I := CollapseBasicCondition×↥(Set.Iio b)
  have hI : Cardinal.mk I<GroundContinuumSucc := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt groundContinuumSucc_regular_r392.1
      (basicValue_card_le_continuum_r401.trans_lt (Order.lt_succ _))
      (continuumSuccInitial_card_lt_r406 b)
  obtain ⟨c,hc⟩ := continuumSuccIndex_family_bounded_r399
    (fun z : I => collapseNameCode (z.1,z.2.val)) hI
  exact ⟨c,fun p i hi => hc (p,⟨i,hi⟩)⟩

def codeClosedAt (b : GroundContinuumSuccIndex) : Prop :=
  ∀ p : CollapseBasicCondition,∀ i<b,collapseNameCode (p,i)<b

noncomputable def encodeProfile (s : SmallDiamondCondition) (A : GroundContinuumSuccIndex→PreparedBA)
    (b : GroundContinuumSuccIndex) : Set GroundContinuumSuccIndex :=
  {z | ∃ (p : CollapseBasicCondition) (i : GroundContinuumSuccIndex),
    i<b ∧ p∈positiveCut s (A i) ∧ collapseNameCode (p,i)=z}

theorem encodeProfile_supported_r406 (s : SmallDiamondCondition)
    (A : GroundContinuumSuccIndex→PreparedBA) (b : GroundContinuumSuccIndex) (hb : codeClosedAt b) :
    ∀ z∈encodeProfile s A b,z<b := by
  rintro z ⟨p,i,hi,_,rfl⟩
  exact hb p i hi

theorem code_mem_encodeProfile_r406 (s : SmallDiamondCondition)
    (A : GroundContinuumSuccIndex→PreparedBA) {b i : GroundContinuumSuccIndex} (hi : i<b)
    (p : CollapseBasicCondition) :
    collapseNameCode (p,i)∈encodeProfile s A b ↔ p∈positiveCut s (A i) := by
  constructor
  · rintro ⟨r,j,_,hr,he⟩
    have h := collapseNameCode.injective he
    have hR : r=p := congrArg Prod.fst h
    have hJ : j=i := congrArg Prod.snd h
    simpa only [hR,hJ] using hr
  · intro hp
    exact ⟨p,i,hi,hp,rfl⟩

end PreparedModel
end JSP000933
