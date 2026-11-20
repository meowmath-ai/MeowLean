import JSP000933RelativeSmallQuotientCH
import JSP000933CompleteValueMap

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion

variable {B C I J N : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

noncomputable def MixedEnumeration.push_r470 (E : MixedEnumeration I J B)
    (f : J→N) (hf : Function.Surjective f) : MixedEnumeration I N B where
  cell i n := ⨆ j : {j : J // f j=n},E.cell i j.val
  rowFull i := by
    apply top_unique
    rw [← E.rowFull i]
    apply iSup_le
    intro j
    exact le_iSup_of_le (f j) (le_iSup (fun k : {k : J // f k = f j} => E.cell i k.val) ⟨j,rfl⟩)
  colFull n := by
    obtain ⟨j,hj⟩ := hf n
    apply top_unique
    rw [← E.colFull j]
    apply iSup_le
    intro i
    exact le_iSup_of_le i (le_iSup (fun k : {k : J // f k = n} => E.cell i k.val) ⟨j,hj⟩)
  rowApart i := by
    intro n k hnk
    apply disjoint_iff_inf_le.mpr
    rw [iSup_inf_iSup]
    apply iSup_le
    rintro ⟨u,v⟩
    have hn : u.val≠v.val := fun he =>
      hnk (u.property.symm.trans ((congrArg f he).trans v.property))
    exact disjoint_iff_inf_le.mp (E.rowApart i hn)

def MixedEnumeration.reindex_r470 (E : MixedEnumeration I N B) (f : J≃I) :
    MixedEnumeration J N B where
  cell j n := E.cell (f j) n
  rowFull j := E.rowFull (f j)
  colFull n := by
    apply top_unique
    rw [← E.colFull n]
    apply iSup_le
    intro i
    exact le_iSup_of_le (f.symm i) (by rw [f.apply_symm_apply])
  rowApart j := E.rowApart (f j)

noncomputable def MixedEnumeration.map_r470 (E : MixedEnumeration I N B) (F : CompleteValueMap B C) :
    MixedEnumeration I N C where
  cell i n := F.toFun (E.cell i n)
  rowFull i := by rw [← F.map_iSup,E.rowFull,F.map_top]
  colFull n := by rw [← F.map_iSup,E.colFull,F.map_top]
  rowApart i := by
    intro n k h
    apply disjoint_iff_inf_le.mpr
    rw [← F.map_inf,(E.rowApart i h).eq_bot,F.map_bot]

end RelativeOCA
end JSP000933
