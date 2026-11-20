import JSP000933PreparedNoCountableCofinality

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanNames

theorem exists_groundOmegaOne_cofinal_r423 (d : GroundContinuumSuccIndex)
    (hd : OmegaOneCofinalIndex d) :
    ∃ f : BaseOmegaOne.Type→GroundContinuumSuccIndex,
      (∀ j,f j<d) ∧ ∀ a<d,∃ j,a<f j := by
  classical
  let α := continuumSuccOrdinal d
  let I := α.ToType
  change α.cof=ℵ₁ at hd
  have hI : Order.cof I=ℵ₁ := by
    rw [← Ordinal.cof_type,Ordinal.type_toType]
    exact hd
  obtain ⟨S,hS,hType⟩ := Ordinal.exists_ord_cof_eq (α := I)
  have hCard : Cardinal.mk S=ℵ₁ := by
    rw [← Ordinal.card_type ((· < ·) : S→S→Prop)]
    change (Ordinal.type ((· < ·) : S → S → Prop)).card=ℵ₁
    rw [hType,hI,Cardinal.card_ord]
  obtain ⟨enumOmega⟩ := Cardinal.eq.mp (baseOmegaOne_type_card_r391.trans hCard.symm)
  let ord (j : BaseOmegaOne.Type) := (enumOmega j).val.toOrd.val
  have hOrd (j : BaseOmegaOne.Type) : ord j<α := (enumOmega j).val.toOrd.property
  let f (j : BaseOmegaOne.Type) :=
    continuumSuccIndexOf (ord j) ((hOrd j).trans (continuumSuccOrdinal_lt_r392 d))
  have hf (j : BaseOmegaOne.Type) : continuumSuccOrdinal (f j)=ord j :=
    continuumSuccIndexOf_ordinal_r399 _ _
  refine ⟨f,fun j => (continuumSuccIndex_lt_iff_r399 _ _).mpr ((hf j).trans_lt (hOrd j)),?_⟩
  intro a ha
  have hA : continuumSuccOrdinal a<α := (continuumSuccIndex_lt_iff_r399 _ _).mp ha
  have hLimit : Order.IsSuccLimit α := Ordinal.one_lt_cof_iff.mp (Ordinal.aleph0_le_cof_iff.mp
    (by rw [hd]; exact PSet.omega_lt_aleph_one.le))
  let e := Ordinal.ToType.mk (o := α)
  let b : I := e ⟨continuumSuccOrdinal a+1,hLimit.add_one_lt hA⟩
  obtain ⟨z,hz,hbz⟩ := hS b
  let j := enumOmega.symm (⟨z,hz⟩ : S)
  have hZ : (enumOmega j).val=z := by simp [j]
  have hB : continuumSuccOrdinal a+1≤z.toOrd.val := by
    have hh := e.symm.monotone hbz
    change (e.symm b).val≤(e.symm z).val at hh
    simpa [b,Ordinal.ToType.toOrd] using hh
  refine ⟨j,(continuumSuccIndex_lt_iff_r399 _ _).mpr ?_⟩
  rw [hf]
  change continuumSuccOrdinal a<(enumOmega j).val.toOrd.val
  rw [hZ]
  exact (Order.lt_add_one_iff.mpr le_rfl).trans_le hB

theorem prepared_existsOmegaOneCofinal_r423 (d : GroundContinuumSuccIndex)
    (hd : OmegaOneCofinalIndex d) :
    (⊤ : PreparedBA)≤⨆ G : bSet PreparedBA,
      is_func' (check BaseOmegaOne) (preparedOrdinalEntry d) G⊓
        actualCofinalGraph (check BaseOmegaOne) (preparedOrdinalEntry d) G := by
  obtain ⟨f,hLt,hC⟩ := exists_groundOmegaOne_cofinal_r423 d hd
  let D : bSet PreparedBA := preparedOrdinalEntry d
  let X : bSet PreparedBA := check BaseOmegaOne
  let e (j : BaseOmegaOne.Type) : bSet PreparedBA := check (BaseOmegaOne.Func j)
  let v (j : BaseOmegaOne.Type) : bSet PreparedBA := preparedOrdinalEntry (f j)
  let G := functionalGraphName e v
  have hInX (j : BaseOmegaOne.Type) : (⊤ : PreparedBA)≤e j∈ᴮ X :=
    check_mem (PSet.func_mem BaseOmegaOne j)
  have hPair (j : BaseOmegaOne.Type) : (⊤ : PreparedBA)≤pair (e j) (v j)∈ᴮ G :=
    pair_mem_functionalGraph_self_r102 e v j
  apply le_iSup_of_le G
  apply le_inf
  · apply le_inf
    · exact functionValue_functionalGraph_r102 e v
        (fun _ _ hn => checkedDistinct_eq_bot_r412 _ preparedOmegaOne_pset_inj_r413 hn)
    · let F (x : bSet PreparedBA) := ⨆ z : bSet PreparedBA,(z∈ᴮ D)⊓(pair x z∈ᴮ G)
      have hF : B_ext F := B_ext_iSup (h := fun z => B_ext_inf B_ext_const B_ext_pair_mem_left)
      apply (checkedBoundedAll_iff_r418 BaseOmegaOne e (fun j => ⟨j,rfl⟩) hInX ⊤ F hF).mpr
      intro j
      exact le_iSup_of_le (v j) (le_inf (preparedEntry_mem_top_r418 (hLt j)) (hPair j))
  · unfold actualCofinalGraph
    rw [preparedOrdinalEntry_asOrdinal_r416 d]
    let F (a : bSet PreparedBA) := ⨆ n : bSet PreparedBA,(n∈ᴮ X)⊓(
      ⨆ b : bSet PreparedBA,(b∈ᴮ check (PSet.ordinalMk (continuumSuccOrdinal d)))⊓
        ((pair n b∈ᴮ G)⊓(a∈ᴮ b)))
    have hF : B_ext F := B_ext_iSup (h := fun n => B_ext_inf B_ext_const
      (B_ext_iSup (h := fun b => B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_mem_left))))
    apply (checkedBoundedAll_iff_r418 (PSet.ordinalMk (continuumSuccOrdinal d))
      (fun i : ↥(Set.Iio d) => preparedOrdinalEntry i.val) (preparedEntry_basis_r418 d)
      (fun i => by rw [← preparedOrdinalEntry_asOrdinal_r416 d]; exact preparedEntry_mem_top_r418 i.property)
      ⊤ F hF).mpr
    intro a
    obtain ⟨j,hj⟩ := hC a.val a.property
    apply le_iSup_of_le (e j)
    apply le_inf (hInX j)
    apply le_iSup_of_le (v j)
    apply le_inf
    · rw [← preparedOrdinalEntry_asOrdinal_r416 d]
      exact preparedEntry_mem_top_r418 (hLt j)
    · exact le_inf (hPair j) (preparedEntry_mem_top_r418 hj)

end PreparedModel
end JSP000933
