import JSP000933RelativeMixedEnumTransport
import JSP000933PreparedInternalCH

open bSet Cardinal Flypitch
open scoped Flypitch

namespace JSP000933
namespace RelativeOCA

open PreparedModel OpenGraphForcing

noncomputable def preparedCollapseMixedEnum :
    MixedEnumeration (check BaseOmegaOne : bSet PreparedBA).type
      (check BaseGroundReals : bSet PreparedBA).type PreparedBA where
  cell := productCollapseArray
  rowFull := productCollapseArray_tall_r413
  colFull := productCollapseArray_wide_r413
  rowApart i := fun _ _ h => disjoint_iff_inf_le.mpr (productCollapseArray_anti_r413 i h)

theorem prepared_checkedReals_card_r471 :
    Cardinal.mk (check BaseGroundReals : bSet PreparedBA).type=𝔠 := by
  rw [check_type',baseGroundReals_type_card_r391]

theorem prepared_smallMixedTraceEnum_r471 (N : Type) [Nonempty N] (hN : Cardinal.mk N≤𝔠) :
    Nonempty (MixedEnumeration OmegaOneIndex N PreparedBA) := by
  classical
  let I := (check BaseOmegaOne : bSet PreparedBA).type
  let J := (check BaseGroundReals : bSet PreparedBA).type
  have hI : Cardinal.mk I=ℵ₁ := by
    unfold I
    rw [check_type',baseOmegaOne_type_card_r391]
  obtain ⟨e⟩ := Cardinal.eq.mp (mk_OmegaOneIndex_r61.trans hI.symm)
  obtain ⟨emb⟩ := (Cardinal.le_def N J).mp (hN.trans_eq prepared_checkedReals_card_r471.symm)
  let alt : N := Classical.choice inferInstance
  let f (j : J) : N := if h : ∃ n,emb n=j then Classical.choose h else alt
  have hF : Function.Surjective f := by
    intro n
    have hx : ∃ a,emb a=emb n := ⟨n,rfl⟩
    refine ⟨emb n,?_⟩
    apply emb.injective
    simpa only [f,dite_eq_left hx] using Classical.choose_spec hx
  exact ⟨(preparedCollapseMixedEnum.reindex_r470 e).push_r470 f hF⟩

end RelativeOCA
end JSP000933
