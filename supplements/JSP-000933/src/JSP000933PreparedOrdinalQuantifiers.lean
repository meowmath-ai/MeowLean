import JSP000933PreparedActualSuccessor

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

theorem groundOrd_not_mem_of_not_lt_r418 {a d : Ordinal} (h : ¬a<d) :
    PSet.ordinalMk a∉PSet.ordinalMk d := by
  exact fun hm => h (PSet.ordinalMk_lt_of_mem hm)

theorem preparedEntry_mem_top_r418 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    {a d : GroundContinuumSuccIndex} (h : a<d) :
    (⊤ : B)≤(preparedOrdinalEntry a : bSet B)∈ᴮ preparedOrdinalEntry d := by
  rw [preparedOrdinalEntry_asOrdinal_r416,preparedOrdinalEntry_asOrdinal_r416]
  exact check_mem (prepOrdinalMk_mem_of_lt_r397 ((continuumSuccIndex_lt_iff_r399 _ _).mp h))

theorem preparedEntry_mem_bot_r418 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    {a d : GroundContinuumSuccIndex} (h : ¬a<d) :
    ((preparedOrdinalEntry a : bSet B)∈ᴮ preparedOrdinalEntry d)=⊥ := by
  rw [preparedOrdinalEntry_asOrdinal_r416,preparedOrdinalEntry_asOrdinal_r416]
  apply le_bot_iff.mp
  exact check_not_mem (groundOrd_not_mem_of_not_lt_r418
    (fun hh => h ((continuumSuccIndex_lt_iff_r399 _ _).mpr hh))) le_rfl

theorem checkedBoundedAll_iff_r418 {B : Type} [NontrivialCompleteBooleanAlgebra B] {I : Type}
    (S : PSet.{0}) (E : I→bSet B)
    (hBasis : ∀ j : S.Type,∃ i,check (S.Func j)=E i)
    (hMem : ∀ i,(⊤ : B)≤E i∈ᴮ check S)
    (v : B) (F : bSet B→B) (hF : B_ext F) :
    v≤(⨅ x : bSet B,(x∈ᴮ check S)⟹ F x) ↔ ∀ i,v≤F (E i) := by
  constructor
  · intro h i
    exact (le_inf (h.trans (iInf_le _ (E i))) (le_top.trans (hMem i))).trans Lattice.bv_imp_elim
  · intro h
    rw [← bounded_forall (h_congr := hF)]
    apply le_iInf
    intro j
    rw [← deduction,check_bval_top,inf_top_eq,check_func]
    obtain ⟨i,hi⟩ := hBasis (check_cast j)
    rw [hi]
    exact h i

theorem checkedBoundedExists_eq_r418 {B : Type} [NontrivialCompleteBooleanAlgebra B] {I : Type}
    (S : PSet.{0}) (E : I→bSet B)
    (hBasis : ∀ j : S.Type,∃ i,check (S.Func j)=E i)
    (hMem : ∀ i,(⊤ : B)≤E i∈ᴮ check S)
    (F : bSet B→B) (hF : B_ext F) :
    (⨆ x : bSet B,(x∈ᴮ check S)⊓F x)=⨆ i,F (E i) := by
  apply le_antisymm
  · rw [← bounded_exists (h_congr := hF)]
    apply iSup_le
    intro j
    rw [check_bval_top,top_inf_eq,check_func]
    obtain ⟨i,hi⟩ := hBasis (check_cast j)
    rw [hi]
    exact le_iSup (fun k => F (E k)) i
  · apply iSup_le
    intro i
    exact le_iSup_of_le (E i) (le_inf (le_top.trans (hMem i)) le_rfl)

theorem preparedKappa_basis_r418 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (j : BaseSuccPSet.Type) :
    ∃ i : GroundContinuumSuccIndex,(check (BaseSuccPSet.Func j) : bSet B)=preparedOrdinalEntry i :=
  ⟨baseSuccIndexEquiv.symm j,by simp [preparedOrdinalEntry]⟩

theorem preparedKappa_mem_r418 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (i : GroundContinuumSuccIndex) :
    (⊤ : B)≤(preparedOrdinalEntry i : bSet B)∈ᴮ check BaseSuccPSet :=
  check_mem (PSet.func_mem BaseSuccPSet (baseSuccIndexEquiv i))

theorem preparedEntry_basis_r418 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (d : GroundContinuumSuccIndex) (j : (PSet.ordinalMk (continuumSuccOrdinal d)).Type) :
    ∃ i : ↥(Set.Iio d),(check ((PSet.ordinalMk (continuumSuccOrdinal d)).Func j) : bSet B)=
      preparedOrdinalEntry i.val := by
  let u : (continuumSuccOrdinal d).ToType := cast PSet.ordinalMk_type j
  let i := continuumSuccIndexOf u.toOrd.val (u.toOrd.property.trans (continuumSuccOrdinal_lt_r392 d))
  have hOrd : continuumSuccOrdinal i=u.toOrd.val := continuumSuccIndexOf_ordinal_r399 _ _
  have hi : i<d := (continuumSuccIndex_lt_iff_r399 _ _).mpr (hOrd.trans_lt u.toOrd.property)
  refine ⟨⟨i,hi⟩,?_⟩
  change (check ((PSet.ordinalMk (continuumSuccOrdinal d)).Func j) : bSet B)=preparedOrdinalEntry i
  rw [preparedOrdinalEntry_asOrdinal_r416,hOrd,ordinalMk_func_eq_r396]

end PreparedModel
end JSP000933
