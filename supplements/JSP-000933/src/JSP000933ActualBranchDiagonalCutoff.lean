import JSP000933ActualLargeBranchDomain

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def shortBranchCut (j : ℕ) : ℕ :=
  (Finset.range (j+1)).sup (fun k =>
    (Finset.univ : Finset (Fin k → Bool)).sup
      (fun f => justSourceStart (Encodable.encode (List.ofFn f)+1)))

theorem shortBranchCut_bounds_r265 (j : ℕ) (u : Word) (m : ℕ)
    (hu : u.length≤j) (hm : m∈justSourceBlock (Encodable.encode u)) : m<shortBranchCut j := by
  let f : Fin u.length → Bool := fun i => u[i.val]
  have hF := Finset.le_sup (f := fun f : Fin u.length → Bool =>
    justSourceStart (Encodable.encode (List.ofFn f)+1)) (Finset.mem_univ f)
  have he : List.ofFn f=u := List.ofFn_getElem
  rw [he] at hF
  have hK := Finset.le_sup (f := fun k : ℕ => (Finset.univ : Finset (Fin k → Bool)).sup
    (fun f => justSourceStart (Encodable.encode (List.ofFn f)+1)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hu))
  have hm' : m∈Finset.Ico (justSourceStart (Encodable.encode u))
      (justSourceStart (Encodable.encode u+1)) := hm
  exact (Finset.mem_Ico.mp hm').2.trans_le (hF.trans hK)

theorem actualBranches_opposed_noCommonLate_r265 (x y : ℕ → B) (j m : ℕ)
    {p : B} (hop : p≤bitEq (x j) (y j)ᶜ) (hm : shortBranchCut j≤ m) :
    p⊓(actualBranchBits x m⊓actualBranchBits y m)≤⊥ := by
  apply le_of_dense_named_refinements_r219
  intro q hq hQ
  obtain ⟨u,s,hs,hsq,hS⟩ := exists_nonzero_below_choice_r135 q hq
    (fun w : {w : Word // m∈justSourceBlock (Encodable.encode w)} => cylinderValue x w.1)
    (hQ.trans (inf_le_right.trans inf_le_left))
  obtain ⟨v,t,ht,hts,hT⟩ := exists_nonzero_below_choice_r135 s hs
    (fun w : {w : Word // m∈justSourceBlock (Encodable.encode w)} => cylinderValue y w.1)
    (hsq.trans (hQ.trans (inf_le_right.trans inf_le_right)))
  have he : Encodable.encode u.val=Encodable.encode v.val := by
    by_contra hne
    exact Finset.disjoint_left.mp (justSourceBlock_pairwise hne) u.property v.property
  have hWord : u.val=v.val := Encodable.encode_injective he
  have hj : j<u.val.length := by
    by_contra hn
    exact (not_lt_of_ge hm) (shortBranchCut_bounds_r265 j u.val m (Nat.le_of_not_gt hn) u.property)
  have hCyl : t≤cylinderValue y u.val := by
    rw [hWord]
    exact hT
  have hMatch := sameCylinder_mask_r261 (hts.trans hS) hCyl j hj
  have hP : t≤p := hts.trans (hsq.trans (hQ.trans inf_le_left))
  have hOpp := (le_bitEq_iff_r126 t _ _).mp (hP.trans hop)
  have hE : t⊓y j=t⊓(y j)ᶜ := hMatch.symm.trans hOpp
  have h0 : t⊓y j≤⊥ :=
    (le_inf inf_le_right (hE.le.trans inf_le_right)).trans_eq inf_compl_eq_bot'
  have h1 : t⊓(y j)ᶜ≤⊥ := hE.symm.le.trans h0
  have hBot : t≤⊥ := calc
    t = t⊓(y j⊔(y j)ᶜ) := by rw [sup_compl_eq_top,inf_top_eq]
    _ = (t⊓y j)⊔(t⊓(y j)ᶜ) := inf_sup_left _ _ _
    _ ≤ ⊥ := sup_le h0 h1
  exact (ht (le_bot_iff.mp hBot)).elim

abbrev SampleSlot := ℕ × ℕ × Word

noncomputable def actualFreshBranch (support : SampleSlot → ℕ → B) (i : ℕ) : B :=
  match Encodable.decode (α := SampleSlot) i with
  | none => ⊥
  | some s => (support s i)ᶜ

@[simp] theorem actualFreshBranch_at_slot_r265 (support : SampleSlot → ℕ → B) (slot : SampleSlot) :
    actualFreshBranch support (Encodable.encode slot)=(support slot (Encodable.encode slot))ᶜ := by
  simp only [actualFreshBranch,Encodable.encodek]

theorem actualFreshBranch_avoids_supportCap_r265 (support : SampleSlot → ℕ → B)
    (slot : SampleSlot) (cap : ℕ → B) {p : B}
    (hCap : p≤bitsBelowValue cap (actualBranchBits (support slot))) (m : ℕ)
    (hm : shortBranchCut (Encodable.encode slot)≤ m) :
    p⊓(cap m⊓actualBranchBits (actualFreshBranch support) m)≤⊥ := by
  let j := Encodable.encode slot
  have hOpp : p≤bitEq (actualFreshBranch support j) (support slot j)ᶜ :=
    (le_bitEq_iff_r126 p _ _).mpr
      (congrArg (fun b : B => p⊓b) (actualFreshBranch_at_slot_r265 support slot))
  have hNo := actualBranches_opposed_noCommonLate_r265
    (actualFreshBranch support) (support slot) j m hOpp hm
  have hSub : p⊓(cap m⊓actualBranchBits (actualFreshBranch support) m)≤
      p⊓(actualBranchBits (actualFreshBranch support) m⊓actualBranchBits (support slot) m) :=
    le_inf inf_le_left (le_inf (inf_le_right.trans inf_le_right)
      ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (bitsBelowValue_apply_r256 hCap m)))
  exact hSub.trans hNo

end SetLanguage
end JSP000933
