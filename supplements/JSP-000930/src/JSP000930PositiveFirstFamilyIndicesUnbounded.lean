import JSP000930PositiveUnboundedEvaluationsContradiction

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanNames JSP000933.PreparedModel JSP000933.RelativeOCA
  JSP000933.BooleanCompletion
open JSP000930.Positive.Cohen

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

theorem weightedGraph_total_under_mark
    (x y : I → bSet B) (w : I → B) (D R : bSet B) (m : B)
    (hCover : ∀ a,m ⊓ (a ∈ᴮ D) ≤ ⨆ i,w i ⊓ (a =ᴮ x i))
    (hRange : ∀ i,w i ≤ y i ∈ᴮ R) :
    m ≤ is_total D R (weightedGraph x y w) := by
  apply le_iInf
  intro a
  rw [← _root_.deduction]
  apply (hCover a).trans
  apply iSup_le
  intro i
  apply le_iSup_of_le (y i)
  refine le_inf (inf_le_left.trans (hRange i)) ?_
  rw [pair_mem_weightedGraph]
  apply le_iSup_of_le i
  exact le_inf inf_le_left (le_inf inf_le_right bv_refl)

noncomputable def firstFamilyIndices
    (x : GroundContinuumSuccIndex → bSet B) (F : bSet B)
    (i : GroundContinuumSuccIndex) : B :=
  firstNamedOccurrence x i ⊓ (x i ∈ᴮ F)

theorem firstFamilyIndices_cover (x : GroundContinuumSuccIndex → bSet B) (F : bSet B)
    (h : ∀ a,(a ∈ᴮ F) ≤ ⨆ i,a =ᴮ x i) (a : bSet B) :
    (a ∈ᴮ F) ≤ ⨆ i,firstFamilyIndices x F i ⊓ (a =ᴮ x i) := by
  apply (le_inf le_rfl ((h a).trans (firstNamedOccurrence_covers x a))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  let d := (a ∈ᴮ F) ⊓ (firstNamedOccurrence x i ⊓ (a =ᴮ x i))
  have hM : d ≤ x i ∈ᴮ F :=
    subst_congr_mem_left' (inf_le_right.trans inf_le_right) inf_le_left
  exact le_inf (le_inf (inf_le_right.trans inf_le_left) hM)
    (inf_le_right.trans inf_le_right)

theorem not_small_family_first_indices_unbounded
    (F₀ : CompleteValueMap PreparedBA B)
    (x : GroundContinuumSuccIndex → bSet B) (F : bSet B)
    (h : ∀ a,(a ∈ᴮ F) ≤ ⨆ i,a =ᴮ x i)
    (p : B) (hp : p ≤ (injects_into F (check BaseOmegaOne))ᶜ) :
    p ≤ unboundedKappaValue (firstFamilyIndices x F) := by
  classical
  apply le_iInf
  intro β
  let A := firstFamilyIndices x F
  let U := aboveKappaValue A β
  change p ≤ U
  by_contra he
  let m := p ⊓ Uᶜ
  have hm : m ≠ ⊥ := fun h0 =>
    he (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr h0.le))
  obtain ⟨d⟩ := kappa_above_nonempty β
  let J := {i : GroundContinuumSuccIndex // i ≤ β}
  let X (i : J) := x i.val
  let Y (i : J) : bSet B := preparedOrdinalEntry i.val
  let W (i : J) := m ⊓ A i.val
  let D : bSet B := preparedOrdinalEntry d.val
  let G := weightedGraph X Y W
  have hF : (⊤ : B) ≤ is_func G := by
    apply weightedGraph_func
    intro i j
    by_cases hij : i.val = j.val
    · have hij' := Subtype.ext hij
      subst j
      exact bv_refl
    · have hh := (firstNamedOccurrence_separates x hij).le
      have hh' : W i ⊓ W j ≤
          firstNamedOccurrence x i.val ⊓ firstNamedOccurrence x j.val :=
        inf_le_inf (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_left)
      exact ((inf_le_inf hh' le_rfl).trans hh).trans bot_le
  have hI : (⊤ : B) ≤ is_inj G := by
    apply weightedGraph_inj
    intro i j
    by_cases hij : i.val = j.val
    · have hij' := Subtype.ext hij
      subst j
      exact bv_refl
    · simp only [Y,preparedOrdinalEntry_eq_bot_r416 hij,inf_bot_eq,bot_le]
  have hT : m ≤ is_total F D G := by
    apply weightedGraph_total_under_mark X Y W F D m
    · intro a
      apply (inf_le_inf_left m (firstFamilyIndices_cover x F h a)).trans
      rw [inf_iSup_eq]
      apply iSup_le
      intro i
      by_cases hi : i ≤ β
      · apply le_iSup_of_le (⟨i,hi⟩ : J)
        dsimp only [W, X]
        change m ⊓ (A i ⊓ (a =ᴮ x i)) ≤ (m ⊓ A i) ⊓ (a =ᴮ x i)
        exact (inf_assoc m (A i) (a =ᴮ x i)).ge
      · have hiU : A i ≤ U := le_iSup (fun j : {j : GroundContinuumSuccIndex // β < j} => A j.val) ⟨i,lt_of_not_ge hi⟩
        have hZ : m ⊓ A i = ⊥ :=
          ((disjoint_compl_left.mono_right hiU).mono_left inf_le_right).eq_bot
        rw [← inf_assoc,hZ,bot_inf_eq]
        exact bot_le
    · intro i
      exact le_top.trans (preparedEntry_mem_top_r418 (i.property.trans_lt d.property))
  have hFirst : m ≤ injects_into F D :=
    le_iSup_of_le G (le_inf (le_inf (le_top.trans hF) hT) (le_top.trans hI))
  have hSmall : m ≤ injects_into F (check BaseOmegaOne) :=
    injects_into_trans hFirst (le_top.trans (checked_predecessor_injects_into_omegaOne F₀ d.val))
  exact hm (disjoint_compl_right.out _ hSmall (inf_le_left.trans hp))

end JSP000930.Positive
