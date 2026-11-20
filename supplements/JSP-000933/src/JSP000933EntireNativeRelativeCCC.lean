import JSP000933NativeLimitCCC
import JSP000933NativeSuccessorCCC
import JSP000933ProjectedOmegaOnePreservation

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport RelativeOCA OpenGraphForcing MarkedForcing

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

theorem basedPrefix_first_projectedCCC
    (tail : BasedTailPolicy A B T) {a : A} (ha : (⊥ : A)<a)
    (hFirst : ∀ i<a, i=⊥) :
    ProjectedAntichainCCC (prefixMaskRealization tail ha).project := by
  classical
  let M := prefixMaskRealization tail ha
  apply M.projectedRowCCC_iff.mp
  intro W hMask hSep
  have hCompat (p q : BasedBefore tail a) (hPos : M.mask p ⊓ M.mask q ≠ ⊥) :
      Compatible p q := by
    let b := M.mask p ⊓ M.mask q
    let r : BasedBefore tail a := ⟨putBase tail p.val b hPos inf_le_left,
      putBase_bounded tail ha p b hPos inf_le_left⟩
    refine ⟨r,putBase_le tail p.val b hPos inf_le_left,?_⟩
    intro i t ht
    have hi : i=⊥ := hFirst i (q.property i ⟨t,ht⟩)
    subst i
    have hT := ((basedPolicy_min_valid tail q.val.trace t).mp (q.val.valid ⊥ t ht)).2
    refine ⟨(b,⊤),by simp [r,putBase,attachTrace],?_⟩
    have hQ : b≤t.1 := by
      have hh : b≤M.mask q := inf_le_right
      simpa only [M,prefixMaskRealization,baseMask,ht,Option.getD_some] using hh
    exact ⟨hQ,by rw [hT]⟩
  apply le_bot_iff.mp
  apply (unboundedValue_le_pairOverlap_r431 _).trans
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  rw [iSup_inf_iSup]
  apply iSup_le
  rintro ⟨p,q⟩
  by_cases hPos : M.mask p ⊓ M.mask q ≠ ⊥
  · exact disjoint_iff_inf_le.mp (hSep i j.val j.property p q (hCompat p q hPos))
  · have hZero : M.mask p ⊓ M.mask q = ⊥ := by by_contra hn; exact hPos hn
    exact (inf_le_inf (hMask i p) (hMask j.val q)).trans hZero.le

theorem below_stage_cases {a : A} (ha : (⊥ : A)<a) :
    (∀ i<a,i=⊥) ∨
    (∃ b, (⊥ : A)<b ∧ b<a ∧ ∀ i : A, i<a ↔ i≤b) ∨
    (∀ i<a, ∃ b, i<b ∧ b<a) := by
  classical
  by_cases h : ∀ i<a, ∃ b,i<b ∧ b<a
  · exact Or.inr (Or.inr h)
  · push Not at h
    obtain ⟨b,hba,hb⟩ := h
    have hPrev (i : A) : i<a ↔ i≤b := by
      constructor
      · intro hi
        exact le_of_not_gt (fun hbi => (not_lt_of_ge (hb i hbi)) hi)
      · exact fun hi => hi.trans_lt hba
    by_cases he : b=⊥
    · exact Or.inl (fun i hi => le_antisymm (he ▸ (hPrev i).mp hi) bot_le)
    · exact Or.inr (Or.inl ⟨b,lt_of_le_of_ne bot_le (Ne.symm he),hba,hPrev⟩)

theorem basedPrefix_all_projectedCCC
    (tail : BasedTailPolicy A B T) (hB : BoundsCountableOmegaOneNames B)
    (hStage : ∀ (a : A) (ha : (⊥ : A)<a),
      ProjectedAntichainCCC (prefixMaskRealization tail ha).project →
      ∃ hMono : Monotone (TailStageValues tail (a := a)),
        ∃ hTop : TailStageValues tail (a := a) ⊤ = ⊤,
          ForcesRelativeCCC (ExactTailIterand tail hMono hTop))
    (a : A) (ha : (⊥ : A)<a) :
    ProjectedAntichainCCC (prefixMaskRealization tail ha).project := by
  revert ha
  refine wellFounded_lt.induction (C := fun a => ∀ ha : (⊥ : A) < a,
    ProjectedAntichainCCC (prefixMaskRealization tail ha).project) a ?_
  · intro a IH ha
    rcases below_stage_cases ha with hFirst|⟨b,hb,hba,hSucc⟩|hLim
    · exact basedPrefix_first_projectedCCC tail ha hFirst
    · have hPrev := IH b hba hb
      obtain ⟨hMono,hTop,hCCC⟩ := hStage b hb hPrev
      exact basedPrefix_successor_projectedCCC tail hb hMono hTop hSucc hPrev hCCC
    · exact basedPrefix_limit_projectedCCC tail hB ha hLim (fun b hb hba => IH b hba hb)

theorem basedWhole_projectedCCC [NoMaxOrder A]
    (tail : BasedTailPolicy A B T) (hB : BoundsCountableOmegaOneNames B)
    (hPrev : ∀ (a : A) (ha : (⊥ : A)<a),
      ProjectedAntichainCCC (prefixMaskRealization tail ha).project) :
    ProjectedAntichainCCC (basedMaskRealization tail).project := by
  classical
  let J := {a : A // (⊥ : A)<a}
  apply (basedMaskRealization tail).projectedRowCCC_iff.mp
  apply projectedRowCCC_of_finite_support_limit (J := J) (Stage := fun a => BasedBefore tail a.val)
    hB _ _ support
    (fun a p => (prefixMaskRealization tail a.property).mask p)
    (fun _ => Compatible) (fun a p => restrict p a.val)
  · intro r
    have hAbove : ∃ a : A, (⊥ : A)<a ∧ ∀ i∈r,i<a := by
      induction r using Finset.induction_on with
      | empty =>
        obtain ⟨a,ha⟩ := exists_gt (⊥ : A)
        exact ⟨a,ha,by simp⟩
      | insert x r hx ih =>
        obtain ⟨b,hb,hbr⟩ := ih
        obtain ⟨a,ha⟩ := exists_gt (max b x)
        refine ⟨a,hb.trans (lt_of_le_of_lt (le_max_left _ _) ha),?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with h|h
        · exact h.symm ▸ (lt_of_le_of_lt (le_max_right _ _) ha)
        · exact (hbr i h).trans (lt_of_le_of_lt (le_max_left _ _) ha)
    obtain ⟨a,ha,hR⟩ := hAbove
    refine ⟨⟨a,ha⟩,?_⟩
    intro p q hPQ hComp
    apply compatible_of_prefix_and_disjointTail_r76 p q a _ hComp
    intro i hp hq
    apply hR i
    rw [←hPQ,Finset.mem_inter]
    exact ⟨(mem_support_r75 p i).mpr hp,(mem_support_r75 q i).mpr hq⟩
  · intro a p
    exact (baseMask_restrict tail p a.property).ge
  · intro a
    exact (prefixMaskRealization tail a.property).projectedRowCCC_iff.mpr
      (hPrev a.val a.property)

end ForcingTransport
end JSP000933
