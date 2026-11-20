import JSP000933RelativeMixedReals
import JSP000933PreparedCollapseEnumeration
import JSP000933GroundSubsetNames

open bSet Cardinal Flypitch
open scoped Flypitch

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion BooleanNames CantorCodes OpenGraphForcing PreparedModel

open scoped Classical in
noncomputable def preparedGroundArrayBits
    (j : (check BaseGroundReals : bSet PreparedBA).type) : ℕ→PreparedBA :=
  fun n => if (fun a : Set (ULift.{0} ℕ) => (ULift.up n : ULift.{0} ℕ) ∈ a)
    (check_cast (x := BaseGroundReals) j) then ⊤ else ⊥

noncomputable def preparedMixedReal
    (i : (check BaseOmegaOne : bSet PreparedBA).type) : ℕ→PreparedBA :=
  mixIndexedReal (productCollapseArray i) preparedGroundArrayBits

theorem preparedMixedReal_onCell_r440 (i : (check BaseOmegaOne : bSet PreparedBA).type)
    (j : (check BaseGroundReals : bSet PreparedBA).type) :
    productCollapseArray i j≤realEqValue (preparedMixedReal i) (preparedGroundArrayBits j) := by
  apply mixIndexedReal_on_weight_r439
  intro a b h
  exact disjoint_iff_inf_le.mpr (productCollapseArray_anti_r413 i h)

theorem preparedGroundArrayBits_hits_r440 (x : ℕ→Bool) :
    ∃ j : (check BaseGroundReals : bSet PreparedBA).type,
      preparedGroundArrayBits j=(fun n => truthBit (x n)) := by
  classical
  let a : BaseGroundReals.Type := {i : ULift ℕ | x i.down=true}
  let e : (check BaseGroundReals : bSet PreparedBA).type ≃ BaseGroundReals.Type := Equiv.cast check_type'
  let j := e.symm a
  have hj : check_cast j=a := e.apply_symm_apply a
  refine ⟨j,?_⟩
  funext n
  unfold preparedGroundArrayBits
  rw [hj]
  let pred := (fun a : Set (ULift.{0} ℕ) => (ULift.up n : ULift.{0} ℕ) ∈ a) a
  by_cases h : pred
  · rw [ite_eq_left h]
    have hx : x n = true := h
    simp [hx,truthBit]
  · rw [ite_eq_right h]
    have hx : x n = false := Bool.eq_false_iff.mpr (show x n ≠ true from h)
    simp [hx,truthBit]

theorem preparedMixedReal_surjectiveValue_r440 (x : ℕ→PreparedBA) :
    (⨆ i : (check BaseOmegaOne : bSet PreparedBA).type,realEqValue x (preparedMixedReal i))=⊤ := by
  apply top_unique
  rw [← groundBitNames_join_top_r185 preparedProduct_countablyClosed_r401 x]
  apply iSup_le
  intro b
  obtain ⟨j,hj⟩ := preparedGroundArrayBits_hits_r440 b
  rw [←hj]
  let v := realEqValue x (preparedGroundArrayBits j)
  have hV : v≤v⊓(⨆ i,productCollapseArray i j) := by
    rw [productCollapseArray_wide_r413,inf_top_eq]
  apply hV.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  have h1 : v⊓productCollapseArray i j≤realEqValue x (preparedGroundArrayBits j) := inf_le_left
  have h2 : v⊓productCollapseArray i j≤realEqValue (preparedGroundArrayBits j) (preparedMixedReal i) :=
    (inf_le_right.trans (preparedMixedReal_onCell_r440 i j)).trans_eq (realEqValue_symm_r127 _ _)
  exact (le_inf h1 h2).trans (realEqValue_trans_r127 _ _ _)

theorem prepared_internalCH_enumeratesBooleanReals_r440 :
    ∃ e : OmegaOneIndex→ℕ→PreparedBA,EnumeratesBooleanReals e := by
  have hCard : Cardinal.mk (check BaseOmegaOne : bSet PreparedBA).type=ℵ₁ := by
    rw [check_type',baseOmegaOne_type_card_r391]
  obtain ⟨E⟩ := Cardinal.eq.mp (mk_OmegaOneIndex_r61.trans hCard.symm)
  refine ⟨fun i => preparedMixedReal (E i),fun x => ?_⟩
  change (⨆ i, realEqValue x (preparedMixedReal (E i))) = ⊤
  rw [generic_iSup_equiv_r413 E (fun i => realEqValue x (preparedMixedReal i))]
  exact preparedMixedReal_surjectiveValue_r440 x

end RelativeOCA
end JSP000933
