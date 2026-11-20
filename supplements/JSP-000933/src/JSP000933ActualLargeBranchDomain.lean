import JSP000933ActualBranchCylinders

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def lengthBelowCode (N : ℕ) : ℕ :=
  (Finset.range N).sup (fun i => ((Encodable.decode (α := Word) i).map List.length).getD 0) + 1

theorem length_lt_lengthBelowCode_r264 {N : ℕ} (u : Word) (hu : Encodable.encode u<N) :
    u.length<lengthBelowCode N := by
  have h := Finset.le_sup
    (f := fun i => ((Encodable.decode (α := Word) i).map List.length).getD 0)
    (Finset.mem_range.mpr hu)
  rw [Encodable.encodek] at h
  exact Nat.lt_succ_of_le h

theorem code_ge_of_long_enough_r264 (N : ℕ) (u : Word) (h : lengthBelowCode N≤u.length) :
    N≤Encodable.encode u :=
  le_of_not_gt (fun hu => (not_lt_of_ge h) (length_lt_lengthBelowCode_r264 u hu))

noncomputable def actualIncludesBlock (a : ℕ → B) (i : ℕ) : B :=
  ⨅ m : ↥(justSourceBlock i), a m.val

noncomputable def actualLongBlockLarge (a : ℕ → B) : B :=
  ⨅ N : ℕ, ⨆ i : {i : ℕ // N≤ i}, actualIncludesBlock a i.val

noncomputable def actualUnboundedCap (a : ℕ → B) : B :=
  ⨅ N : ℕ, ⨆ m : {m : ℕ // N≤ m}, a m.val

theorem actualBranch_large_r264 (x : ℕ → B) : (⊤ : B)≤actualLongBlockLarge (actualBranchBits x) := by
  unfold actualLongBlockLarge
  apply le_iInf
  intro N
  apply le_of_dense_named_refinements_r219
  intro p hp _
  obtain ⟨u,hu,q,hq,hqp,hQ⟩ := exists_decided_initialWord_r136 x (lengthBelowCode N) p hp
  let i := Encodable.encode u
  have hi : N≤ i := code_ge_of_long_enough_r264 N u hu.ge
  refine ⟨q,hq,hqp,le_iSup_of_le ⟨i,hi⟩ ?_⟩
  unfold actualIncludesBlock
  exact le_iInf (fun m => hQ.trans (cylinder_sourceBlock_in_actualBranch_r263 x u m.val m.property))

theorem actualLarge_unbounded_r264 (a : ℕ → B) :
    actualLongBlockLarge a≤actualUnboundedCap a := by
  unfold actualLongBlockLarge actualUnboundedCap
  apply le_iInf
  intro N
  apply (iInf_le _ N).trans
  apply iSup_le
  intro i
  let m := justSourceStart i.val
  have hi : m∈justSourceBlock i.val := Finset.mem_Ico.mpr ⟨le_rfl,
    justSourceStart_strictMono (Nat.lt_succ_self i.val)⟩
  have hN : N≤ m := i.property.trans ((Nat.le_add_right i.val 2).trans (justSourceStart_growth i.val))
  exact le_iSup_of_le (⟨m,hN⟩ : {j : ℕ // N ≤ j})
    (iInf_le (fun j : ↥(justSourceBlock i.val) => a j.val) ⟨m,hi⟩)

theorem actualUnboundedCap_ext_r264 : RealTestExt (actualUnboundedCap (B := B)) := by
  intro p a b he
  unfold actualUnboundedCap
  apply mask_iInf_congr_r126
  intro N
  exact mask_iSup_congr_r126 (fun m => (le_realEqValue_iff_r126 p a b).mp he m.val)

theorem capNeatValue_of_below_r264 (e : ℕ ↪ Word) {p : B} {a b : ℕ → B}
    (hA : p≤bitsBelowValue a b) (hN : p≤capNeatValue e b) : p≤capNeatValue e a := by
  unfold capNeatValue
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  change p≤(a i⊓a j)ᶜ ⊔ crispTruth B (labelsComparable (e i) (e j))
  apply (le_materialImp_iff_r126 _ _ _).mpr
  exact capNeatValue_test_r256 e b (inf_le_left.trans hN) i j
    ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (bitsBelowValue_apply_r256 hA i))
    ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (bitsBelowValue_apply_r256 hA j))

noncomputable def branchCapExtra (a : ℕ → B) : B :=
  actualUnboundedCap a ⊓ (⨆ x : ℕ → B, bitsBelowValue a (actualBranchBits x))

theorem branchCapExtra_ext_r264 : RealTestExt (branchCapExtra (B := B)) := by
  intro p a b he
  unfold branchCapExtra
  exact mask_inf_congr_r126 (actualUnboundedCap_ext_r264 p a b he)
    (mask_iSup_congr_r126 (fun x => bitsBelowValue_mask_r256 he
      (le_top.trans_eq (realEqValue_refl_r127 (actualBranchBits x)).symm)))

theorem exists_actualBranch_support_r264 {p : B} (a : ℕ → B)
    (h : p≤branchCapExtra a) : ∃ x : ℕ → B, p≤bitsBelowValue a (actualBranchBits x) := by
  apply exists_realName_maximum_r138 (fun x => bitsBelowValue a (actualBranchBits x)) ?_ p
    (h.trans inf_le_right)
  intro q x y he
  exact bitsBelowValue_mask_r256 (le_top.trans_eq (realEqValue_refl_r127 a).symm)
    (actualBranchBits_mask_r263 he)

end SetLanguage
end JSP000933
