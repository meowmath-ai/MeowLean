import JSP000930NegativeCountableCofinalDenseUnion
import JSP000933CountableChoiceProfiles

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.OpenGraphForcing JSP000933.RelativeOCA
  JSP000933.PreparedModel

def CheckedOmegaOneLimit (d : OmegaOneIndex) : Prop :=
  ∃ a : ℕ → OmegaOneIndex,StrictMono a ∧ (∀ n,a n < d) ∧
    ∀ b < d,∃ n,b < a n

theorem checkedOmegaOne_increasing_limit
    (a : ℕ → OmegaOneIndex) (ha : StrictMono a) :
    ∃ d : OmegaOneIndex,(∀ n,a n < d) ∧ ∀ b < d,∃ n,b < a n := by
  let U : Set OmegaOneIndex := {d | ∀ n,a n < d}
  obtain ⟨c,hc⟩ := OmegaOneIndex_countable_bounded_r61 (Set.range a) (Set.countable_range a)
  have hU : U.Nonempty := ⟨c,fun n => hc _ (Set.mem_range_self n)⟩
  obtain ⟨d,hd,hMin⟩ := wellFounded_lt.has_min U hU
  refine ⟨d,hd,fun b hb => ?_⟩
  by_contra hn
  have hOrd (n : ℕ) : a n ≤ b := le_of_not_gt (fun hn' => hn ⟨n,hn'⟩)
  have hB : b ∈ U := fun n => (ha (Nat.lt_succ_self n)).trans_le (hOrd (n+1))
  exact (hMin b hB) hb

variable {P : Type} [Preorder P]

theorem choose_fiber_bounds_below_bigger_checked
    (hP : IsCountablyClosed P) (r : P) (d : OmegaOneIndex)
    (W : OmegaOneIndex → OmegaOneIndex → RO P)
    (h : ∀ a < d,imageCondition r ≤ ⨆ b,(aboveValue (fun j => W j a) b)ᶜ) :
    ∃ (q : P) (e : OmegaOneIndex),q ≤ r ∧ d < e ∧
      ∀ a < d,∃ b < e,imageCondition q ≤ (aboveValue (fun j => W j a) b)ᶜ := by
  classical
  let I := {a : OmegaOneIndex // a < d}
  by_cases hI : Nonempty I
  · letI : Nonempty I := hI
    letI : Countable I := OmegaOneIndex_initial_countable_r61 d
    obtain ⟨f,hf⟩ := exists_surjective_nat I
    let V (n : ℕ) (b : OmegaOneIndex) := (aboveValue (fun j => W j (f n).val) b)ᶜ
    obtain ⟨q,g,hqr,hg⟩ := exists_allChoiceProfiles_r411 hP r V
      (fun n => h (f n).val (f n).property)
    obtain ⟨e,he⟩ := OmegaOneIndex_countable_bounded_r61
      (Set.range g ∪ {d}) ((Set.countable_range g).union (Set.countable_singleton d))
    refine ⟨q,e,hqr,he d (Or.inr (Set.mem_singleton d)),fun a ha => ?_⟩
    obtain ⟨n,hn⟩ := hf (⟨a,ha⟩ : I)
    refine ⟨g n,he _ (Or.inl (Set.mem_range_self n)),?_⟩
    exact (congrArg (fun i : I => (aboveValue (fun j => W j i.val) (g n))ᶜ) hn) ▸ hg n
  · obtain ⟨e,he⟩ := OmegaOneIndex_countable_bounded_r61 {d} (Set.countable_singleton d)
    exact ⟨r,e,le_rfl,he d (Set.mem_singleton d),fun a ha => False.elim (hI ⟨⟨a,ha⟩⟩)⟩

theorem relative_regressive_limit_rows_unbounded
    (hP : IsCountablyClosed P) (m : RO P)
    (W : OmegaOneIndex → OmegaOneIndex → RO P)
    (hW : ∀ d,CheckedOmegaOneLimit d → m ≤
      ⨆ a : {a : OmegaOneIndex // a < d},W d a.val) :
    m ≤ ⨆ a,unboundedValue (fun j => W j a) := by
  classical
  let b := ⨆ a,unboundedValue (fun j => W j a)
  change m ≤ b
  by_contra hn
  let u := m ⊓ bᶜ
  have hu : u ≠ ⊥ := fun he => hn
    (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨r,hr⟩ := imageCondition_dense_r50 u hu
  have hF (a : OmegaOneIndex) :
      imageCondition r ≤ ⨆ c,(aboveValue (fun j => W j a) c)ᶜ := by
    have h : imageCondition r ≤ (unboundedValue (fun j => W j a))ᶜ :=
      (hr.trans inf_le_right).trans (compl_le_compl (le_iSup (fun t : OmegaOneIndex => unboundedValue (fun j => W j t)) a))
    simpa only [unboundedValue,compl_iInf] using h
  let R := {p : P // p ≤ r}
  have step (p : R) (d : OmegaOneIndex) :
      ∃ (q : R) (e : OmegaOneIndex),q.val ≤ p.val ∧ d < e ∧
        ∀ a < d,∃ c < e,imageCondition q.val ≤ (aboveValue (fun j => W j a) c)ᶜ := by
    obtain ⟨q,e,hq,hde,hh⟩ := choose_fiber_bounds_below_bigger_checked hP p.val d W
      (fun a _ => (imageCondition_mono_r50 p.property).trans (hF a))
    exact ⟨⟨q,hq.trans p.property⟩,e,hq,hde,hh⟩
  choose next ord hNext hOrd hBounds using step
  let initial : OmegaOneIndex := Classical.choice (show Nonempty OmegaOneIndex from
    Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos))
  let s : ℕ → R × OmegaOneIndex := Nat.rec (⟨r,le_rfl⟩,initial)
    (fun _ p => (next p.1 p.2,ord p.1 p.2))
  have hAnti : Antitone (fun n => (s n).1.val) := by
    apply antitone_nat_of_succ_le
    intro n
    exact hNext (s n).1 (s n).2
  have hMono : StrictMono (fun n => (s n).2) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hOrd (s n).1 (s n).2
  obtain ⟨q,hq⟩ := hP (fun n => (s n).1.val) hAnti
  obtain ⟨d,hAll,hCof⟩ := checkedOmegaOne_increasing_limit (fun n => (s n).2) hMono
  have hqm : imageCondition q ≤ m :=
    (imageCondition_mono_r50 (hq 0)).trans (hr.trans inf_le_left)
  have hE := hqm.trans (hW d ⟨_,hMono,hAll,hCof⟩)
  have hZero : imageCondition q ⊓ (⨆ a : {a : OmegaOneIndex // a < d},W d a.val) = ⊥ := by
    apply le_bot_iff.mp
    rw [inf_iSup_eq]
    apply iSup_le
    intro a
    obtain ⟨n,hn⟩ := hCof a.val a.property
    obtain ⟨c,hc,hB⟩ := hBounds (s n).1 (s n).2 a.val hn
    have hd : c < d := hc.trans (hAll (n+1))
    have hqB := (imageCondition_mono_r50 (hq (n+1))).trans hB
    have hA : imageCondition q ≤ (W d a.val)ᶜ :=
      hqB.trans (compl_le_compl (le_iSup (fun j : {j : OmegaOneIndex // c < j} => W j.val a.val) ⟨d,hd⟩))
    exact (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp hA))
  exact imageCondition_ne_bot_r50 q ((inf_eq_left.mpr hE).symm.trans hZero)

end JSP000930.Negative
