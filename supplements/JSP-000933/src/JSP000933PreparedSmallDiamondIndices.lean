import JSP000933PreparedActualSuccessorRegular

open Cardinal Flypitch

namespace JSP000933
namespace PreparedModel

noncomputable def continuumSuccIndexOf (α : Ordinal) (h : α<GroundContinuumSucc.ord) :
    GroundContinuumSuccIndex := Ordinal.ToType.mk ⟨α,h⟩

@[simp] theorem continuumSuccIndexOf_ordinal_r399 (α : Ordinal) (h : α<GroundContinuumSucc.ord) :
    continuumSuccOrdinal (continuumSuccIndexOf α h)=α := by
  simp [continuumSuccOrdinal,continuumSuccIndexOf]

theorem continuumSuccIndex_lt_iff_r399 (a b : GroundContinuumSuccIndex) :
    a<b ↔ continuumSuccOrdinal a<continuumSuccOrdinal b := by
  let e := Ordinal.ToType.mk (o := GroundContinuumSucc.ord)
  constructor
  · intro h
    exact e.symm.strictMono h
  · intro h
    have he : e.symm a<e.symm b := h
    simpa only [OrderIso.apply_symm_apply] using e.strictMono he

theorem continuumSuccIndex_le_iff_r399 (a b : GroundContinuumSuccIndex) :
    a≤b ↔ continuumSuccOrdinal a≤continuumSuccOrdinal b := by
  constructor
  · intro h
    exact le_of_not_gt (fun hl => not_lt_of_ge h
      ((continuumSuccIndex_lt_iff_r399 b a).mpr hl))
  · intro h
    exact le_of_not_gt (fun hl => not_lt_of_ge h
      ((continuumSuccIndex_lt_iff_r399 b a).mp hl))

theorem continuumSuccIndex_injective_r399 : Function.Injective continuumSuccOrdinal := by
  intro a b he
  let e := Ordinal.ToType.mk (o := GroundContinuumSucc.ord)
  exact e.symm.injective (Subtype.ext he)

theorem continuumSuccIndex_family_bounded_r399 {I : Type} (f : I → GroundContinuumSuccIndex)
    (hI : Cardinal.mk I<GroundContinuumSucc) :
    ∃ b : GroundContinuumSuccIndex, ∀ i, f i<b := by
  let g (i : I) := continuumSuccOrdinal (f i)
  have hC : Cardinal.mk I<GroundContinuumSucc.ord.cof :=
    hI.trans_eq groundContinuumSucc_regular_r392.cof_ord.symm
  have hS : (⨆ i, g i)<GroundContinuumSucc.ord :=
    Ordinal.iSup_lt_of_lt_cof hC (fun i => continuumSuccOrdinal_lt_r392 (f i))
  let α := (⨆ i, g i)+1
  have hα : α<GroundContinuumSucc.ord :=
    (Cardinal.isSuccLimit_ord groundContinuumSucc_regular_r392.1).add_one_lt hS
  refine ⟨continuumSuccIndexOf α hα,fun i => ?_⟩
  apply (continuumSuccIndex_lt_iff_r399 _ _).mpr
  rw [continuumSuccIndexOf_ordinal_r399]
  exact (Ordinal.le_iSup g i).trans_lt (Order.lt_add_one_iff.mpr le_rfl)

structure SmallDiamondCondition where
  length : GroundContinuumSuccIndex
  guesses : (i : GroundContinuumSuccIndex) → i<length → Set GroundContinuumSuccIndex
  supported : ∀ i h j, j∈guesses i h → j< i

def SmallDiamondCondition.Extends (q p : SmallDiamondCondition) : Prop :=
  ∃ h : p.length≤q.length, ∀ i (hi : i<p.length),
    q.guesses i (hi.trans_le h)=p.guesses i hi

instance : Preorder SmallDiamondCondition where
  le := SmallDiamondCondition.Extends
  le_refl p := ⟨le_rfl,fun _ _ => rfl⟩
  le_trans p q r hp hq :=
    ⟨hq.1.trans hp.1,fun i hi => (hp.2 i (hi.trans_le hq.1)).trans (hq.2 i hi)⟩

theorem SmallDiamondCondition.length_mono_r399 {q p : SmallDiamondCondition} (h : q≤p) :
    p.length≤q.length := h.1

noncomputable def emptySmallDiamond : SmallDiamondCondition where
  length := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
  guesses _ _ := ∅
  supported _ _ _ h := False.elim h

theorem smallDiamond_le_empty_r399 (p : SmallDiamondCondition) : p≤emptySmallDiamond := by
  have hLen : emptySmallDiamond.length≤p.length := by
    apply (continuumSuccIndex_le_iff_r399 _ _).mpr
    simp [emptySmallDiamond]
  refine ⟨hLen,fun i hi => False.elim ?_⟩
  have hh := (continuumSuccIndex_lt_iff_r399 i emptySmallDiamond.length).mp hi
  simpa [emptySmallDiamond] using hh

end PreparedModel
end JSP000933
