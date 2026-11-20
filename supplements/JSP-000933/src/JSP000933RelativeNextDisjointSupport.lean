import JSP000933RelativeSupportObstacles

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]

def laterSupportDisjoint (x y : (SupportCandidate I)) : Prop :=
  x.1<y.1 ∧ Disjoint x.2 y.2

open scoped Classical in
noncomputable def laterSupportDisjointValue (x y : (SupportCandidate I)) : B :=
  if laterSupportDisjoint x y then ⊤ else ⊥

noncomputable def rowSupportWeight (W : OmegaOneIndex→Finset I→B)
    (i : OmegaOneIndex) : B :=
  ⨆ s,W i s

theorem priorBound_implies_laterSupportDisjoint_c14
    (W : OmegaOneIndex→Finset I→B) {m : B}
    (C : DiscreteChoiceOn (SupportCandidate I) m) (b : OmegaOneIndex)
    (y : (SupportCandidate I)) (hy : b<y.1) (r : B)
    (hC : r≤priorMixedSupportBound W C b) (hY : r≤W y.1 y.2) :
    r≤guardByChoice C (fun x => laterSupportDisjointValue x y) := by
  classical
  apply le_iInf
  intro x
  apply (le_materialImp_iff_r126 _ _ _).mpr
  let u := r⊓C.value x
  have hX : u≤priorSupportBound W x b :=
    (inf_le_inf hC le_rfl).trans (guardByChoice_elim_r445 C (fun x => priorSupportBound W x b) x)
  by_cases hx : x.1≤b
  · by_cases hd : Disjoint x.2 y.2
    · simp only [laterSupportDisjointValue,ite_eq_left (show laterSupportDisjoint x y from ⟨hx.trans_lt hy,hd⟩),le_top]
    · have he : ∃ v,v∈x.2 ∧ v∈y.2 := by
        by_contra hn
        apply hd
        apply Finset.disjoint_left.mpr
        intro v h1 h2
        exact hn ⟨v,h1,h2⟩
      obtain ⟨v,hv,hv'⟩ := he
      have hA : u≤aboveValue (supportFiber W v) b := (inf_le_left.trans hY).trans
        (le_iSup_of_le (⟨y.1,hy⟩ : {i : OmegaOneIndex // b < i})
          (le_iSup (fun s : {s : Finset I // v ∈ s} => W y.1 s.val) ⟨y.2,hv'⟩))
      have hN : u≤(aboveValue (supportFiber W v) b)ᶜ :=
        hX.trans (inf_le_right.trans (iInf_le (fun z : ↥x.2 => (aboveValue (supportFiber W z.val) b)ᶜ) ⟨v,hv⟩))
      exact ((le_inf hA hN).trans_eq inf_compl_eq_bot').trans bot_le
  · have h0 : u≤⊥ := hX.trans (by
      unfold priorSupportBound
      rw [ite_eq_right hx,bot_inf_eq])
    exact h0.trans bot_le

theorem exists_nextDisjointSupport_c14 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset I→B) (m : B)
    (hUnbounded : m≤unboundedValue (rowSupportWeight W))
    (hFibers : ∀ v,m≤(unboundedValue (supportFiber W v))ᶜ)
    {J : Type} [Countable J] (old : J→DiscreteChoiceOn (SupportCandidate I) m) :
    ∃ C : DiscreteChoiceOn (SupportCandidate I) m,
      (∀ y,C.value y≤W y.1 y.2) ∧
      ∀ j y,C.value y≤guardByChoice (old j) (fun x => laterSupportDisjointValue x y) := by
  let All (b : OmegaOneIndex) := ⨅ j,priorMixedSupportBound W (old j) b
  have hAll : m≤⨆ b,All b :=
    uniform_countable_cutoffs_r444 hB m (fun j => priorMixedSupportBound W (old j))
      (fun j => priorMixedSupportBound_mono_c13 W (old j))
      (fun j => priorMixedSupportBound_covers_c13 hB W m hFibers (old j))
  let U (y : (SupportCandidate I)) := W y.1 y.2⊓
    (⨅ j,guardByChoice (old j) (fun x => laterSupportDisjointValue x y))
  have hU : m≤⨆ y,U y := by
    apply (le_inf le_rfl hAll).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro b
    have hR : m⊓All b≤aboveValue (rowSupportWeight W) b :=
      inf_le_left.trans (hUnbounded.trans (iInf_le _ b))
    apply (le_inf le_rfl hR).trans
    rw [aboveValue,inf_iSup_eq]
    apply iSup_le
    intro i
    rw [rowSupportWeight,inf_iSup_eq]
    apply iSup_le
    intro s
    let y : (SupportCandidate I) := (i.val,s)
    apply le_iSup_of_le y
    apply le_inf inf_le_right
    apply le_iInf
    intro j
    exact priorBound_implies_laterSupportDisjoint_c14 W (old j) b y i.property _
      (inf_le_left.trans (inf_le_right.trans (iInf_le _ j))) inf_le_right
  obtain ⟨C,hC⟩ := exists_discreteChoiceOn_r445 m U hU
  exact ⟨C,fun y => (hC y).trans inf_le_left,
    fun j y => (hC y).trans (inf_le_right.trans (iInf_le _ j))⟩

end RelativeOCA
end JSP000933
