import JSP000930PositiveActualReserveComplexPoint
import JSP000930PositiveOrdinalGapCaps

open bSet Cardinal Lattice Flypitch
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanNames JSP000933.PreparedModel JSP000933.RelativeOCA
  JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem firstFamilyIndices_cover_under_mark (x : GroundContinuumSuccIndex → bSet B) (F : bSet B)
    (p : B) (h : ∀ a,p ⊓ (a ∈ᴮ F) ≤ ⨆ i,a =ᴮ x i) (a : bSet B) :
    p ⊓ (a ∈ᴮ F) ≤ ⨆ i,firstFamilyIndices x F i ⊓ (a =ᴮ x i) := by
  apply (le_inf le_rfl ((h a).trans (firstNamedOccurrence_covers x a))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  let d := (p ⊓ (a ∈ᴮ F)) ⊓ (firstNamedOccurrence x i ⊓ (a =ᴮ x i))
  have hM : d ≤ x i ∈ᴮ F :=
    subst_congr_mem_left' (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right)
  exact le_inf (le_inf (inf_le_right.trans inf_le_left) hM)
    (inf_le_right.trans inf_le_right)

theorem not_small_family_first_indices_unbounded_under_mark
    (F₀ : CompleteValueMap PreparedBA B)
    (x : GroundContinuumSuccIndex → bSet B) (F : bSet B)
    (p : B) (h : ∀ a,p ⊓ (a ∈ᴮ F) ≤ ⨆ i,a =ᴮ x i)
    (hp : p ≤ (injects_into F (check BaseOmegaOne))ᶜ) :
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
  obtain ⟨d⟩ := Cohen.kappa_above_nonempty β
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
      have hmP : m ≤ p := inf_le_left
      have hA : m ⊓ (a ∈ᴮ F) ≤ p ⊓ (a ∈ᴮ F) := inf_le_inf hmP le_rfl
      have hF := hA.trans (firstFamilyIndices_cover_under_mark x F p h a)
      apply (le_inf inf_le_left hF).trans
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

namespace Cohen

theorem checkedOmegaOne_bound_of_actual_reserve_evaluations
    (F : bSet WetzelCohenBA) (code : GroundContinuumSuccIndex → bSet WetzelCohenBA)
    (bits : GroundContinuumSuccIndex → ℕ → WetzelCohenBA) (p : WetzelCohenBA)
    (hCover : ∀ a,p ⊓ (a ∈ᴮ F) ≤ ⨆ i,a =ᴮ code i)
    (heval : ∀ (c : OmegaOneIndex) (q : WetzelCohenBA), q ≠ ⊥ → q ≤ p →
      let A := fun i => firstFamilyIndices code F i ⊓ availableAtReserve (bits i) c
      ∃ (R : bSet WetzelCohenBA) (val : GroundContinuumSuccIndex → bSet WetzelCohenBA),
        q ≤ injects_into R (check BaseOmegaOne) ∧
        (∀ i,q ⊓ A i ≤ val i ∈ᴮ R) ∧
        ∀ i j,i ≠ j → ((q ⊓ A i) ⊓ (q ⊓ A j)) ⊓ (val i =ᴮ val j) = ⊥) :
    p ≤ injects_into F (check BaseOmegaOne) := by
  by_contra hn
  let I := injects_into F (check BaseOmegaOne : bSet WetzelCohenBA)
  let p₀ := p ⊓ Iᶜ
  have hNZ : p₀ ≠ ⊥ := fun e =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr e.le))
  have hCover₀ (a : bSet WetzelCohenBA) : p₀ ⊓ (a ∈ᴮ F) ≤ ⨆ i,a =ᴮ code i :=
    (inf_le_inf (show p₀ ≤ p from inf_le_left) le_rfl).trans (hCover a)
  have hU := not_small_family_first_indices_unbounded_under_mark
    (totalBaseMap wetzelCohenPoset) code F p₀ hCover₀ inf_le_right
  obtain ⟨c,q,hq,hqp,hA⟩ := wetzel_unbounded_active_one_reserve bits
    (firstFamilyIndices code F) p₀ hNZ hU
  obtain ⟨R,val,hSmall,hMembers,hSep⟩ := heval c q hq (hqp.trans inf_le_left)
  have hω : Cardinal.mk BaseOmegaOne.Type < GroundContinuumSucc := by
    rw [baseOmegaOne_type_card_r391]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  exact hq (unbounded_evals_not_inject_small wetzelCohen_boundsKappa BaseOmegaOne hω
    R val _ q hA hMembers hSep hSmall)

end Cohen
end JSP000930.Positive
