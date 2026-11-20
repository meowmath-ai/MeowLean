import JSP000933SimultaneousFreshBranchCovers
import JSP000933SampleSplit

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def sourceSampleLookahead (j k r : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (k+1) × (Fin (4*r) → Bool))).sup
    (fun a => shortBranchCut (Encodable.encode ((j,a.1.val,List.ofFn a.2) : SampleSlot)))

theorem sourceSampleLookahead_bound_r267 (j k r l : ℕ) (u : Word)
    (hl : l≤k) (hu : u.length=4*r) :
    shortBranchCut (Encodable.encode ((j,l,u) : SampleSlot)) ≤ sourceSampleLookahead j k r := by
  let w : Fin (4*r) → Bool := fun i => u[i.val]'(hu.symm ▸ i.isLt)
  have hW : List.ofFn w=u := by
    apply List.ext_getElem (by simp only [List.length_ofFn,hu])
    intro m hm hmu
    rw [List.getElem_ofFn] <;> rfl
  let a : Fin (k+1) × (Fin (4*r) → Bool) := (⟨l,Nat.lt_succ_of_le hl⟩,w)
  have h := Finset.le_sup (f := fun a : Fin (k+1) × (Fin (4*r) → Bool) =>
    shortBranchCut (Encodable.encode ((j,a.1.val,List.ofFn a.2) : SampleSlot))) (Finset.mem_univ a)
  change shortBranchCut (Encodable.encode ((j,l,List.ofFn w) : SampleSlot)) ≤ sourceSampleLookahead j k r at h
  rw [hW] at h
  exact h

theorem actualBranch_meets_bounded_band_r267 (x : ℕ → B) (r R : ℕ)
    (hR : shortBranchCut (lengthBelowCode r)≤R) :
    (⊤ : B)≤⨆ m : {m : ℕ // r≤ m ∧ m<R}, actualBranchBits x m.val := by
  apply le_of_dense_named_refinements_r219
  intro p hp _
  obtain ⟨u,hu,q,hq,hqp,hQ⟩ := exists_decided_initialWord_r136 x (lengthBelowCode r) p hp
  let i := Encodable.encode u
  let m := justSourceStart i
  have hi : r≤ i := code_ge_of_long_enough_r264 r u hu.ge
  have hMem : m∈justSourceBlock i := Finset.mem_Ico.mpr ⟨le_rfl,
    justSourceStart_strictMono (Nat.lt_succ_self i)⟩
  have hMin : r≤ m := hi.trans ((Nat.le_add_right i 2).trans (justSourceStart_growth i))
  have hMax : m<R := (shortBranchCut_bounds_r265 _ u m hu.le hMem).trans_le hR
  exact ⟨q,hq,hqp,le_iSup_of_le ⟨m,hMin,hMax⟩
    (hQ.trans (cylinder_sourceBlock_in_actualBranch_r263 x u m hMem))⟩

noncomputable def actualSampleCut (j : ℕ) : ℕ → ℕ :=
  Nat.rec 0 (fun k r => max (r+1) (max (sourceSampleLookahead j k r) (shortBranchCut (lengthBelowCode r))))

theorem actualSampleCut_zero_r267 (j : ℕ) : actualSampleCut j 0=0 := rfl

theorem actualSampleCut_succ_r267 (j k : ℕ) :
    actualSampleCut j (k+1) =
      max (actualSampleCut j k+1) (max (sourceSampleLookahead j k (actualSampleCut j k))
        (shortBranchCut (lengthBelowCode (actualSampleCut j k)))) := rfl

theorem actualSampleCut_strict_r267 (j : ℕ) : StrictMono (actualSampleCut j) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [actualSampleCut_succ_r267]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem self_le_actualSampleCut_r267 (j k : ℕ) : k≤actualSampleCut j k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt (actualSampleCut_strict_r267 j (Nat.lt_succ_self k)))

theorem actualSampleCut_lookahead_r267 (j k l : ℕ) (u : Word)
    (hl : l≤k) (hu : u.length=4*actualSampleCut j k) :
    shortBranchCut (Encodable.encode ((j,l,u) : SampleSlot))≤actualSampleCut j (k+1) := by
  rw [actualSampleCut_succ_r267]
  exact (sourceSampleLookahead_bound_r267 j k _ l u hl hu).trans
    ((le_max_left _ _).trans (le_max_right _ _))

theorem actualSampleCut_band_nonempty_r267 (x : ℕ → B) (j k : ℕ) :
    (⊤ : B)≤⨆ m : {m : ℕ // actualSampleCut j k≤ m ∧ m<actualSampleCut j (k+1)},
      actualBranchBits x m.val := by
  apply actualBranch_meets_bounded_band_r267
  rw [actualSampleCut_succ_r267]
  exact (le_max_right _ _).trans (le_max_right _ _)

end SetLanguage
end JSP000933
