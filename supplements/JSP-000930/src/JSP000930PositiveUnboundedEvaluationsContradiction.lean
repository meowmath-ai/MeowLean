import JSP000930PositiveNoInjectionUnboundedKappaFamily

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanNames JSP000933.PreparedModel JSP000933.RelativeOCA

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

theorem weightedGraph_total_of_weighted_range
    (x y : I → bSet B) (w : I → B) (D R : bSet B)
    (hCover : ∀ a,(a ∈ᴮ D) ≤ ⨆ i,w i ⊓ (a =ᴮ x i))
    (hRange : ∀ i,w i ≤ y i ∈ᴮ R) :
    (⊤ : B) ≤ is_total D R (weightedGraph x y w) := by
  apply le_iInf
  intro a
  rw [← _root_.deduction,top_inf_eq]
  apply (hCover a).trans
  apply iSup_le
  intro i
  apply le_iSup_of_le (y i)
  refine le_inf (inf_le_left.trans (hRange i)) ?_
  rw [pair_mem_weightedGraph]
  apply le_iSup_of_le i
  exact le_inf inf_le_left (le_inf inf_le_right bv_refl)

theorem unbounded_evals_not_inject_small
    (hB : BoundsSmallKappaNames B)
    (x : PSet.{0}) (hx : Cardinal.mk x.Type < GroundContinuumSucc)
    (R : bSet B) (v : GroundContinuumSuccIndex → bSet B)
    (A : GroundContinuumSuccIndex → B) (m : B)
    (hUnbounded : m ≤ unboundedKappaValue A)
    (hMembers : ∀ i,m ⊓ A i ≤ v i ∈ᴮ R)
    (hSeparated : ∀ i j,i ≠ j → ((m ⊓ A i) ⊓ (m ⊓ A j)) ⊓ (v i =ᴮ v j) = ⊥)
    (hSmall : m ≤ injects_into R (check x)) : m = ⊥ := by
  let w (i : GroundContinuumSuccIndex) := m ⊓ A i
  let e (i : GroundContinuumSuccIndex) : bSet B := preparedOrdinalEntry i
  let T := familyName e w
  have hT : m ≤ unboundedKappaValue (fun i => e i ∈ᴮ T) := by
    apply le_iInf
    intro β
    have hb : m ≤ ⨆ i : {i : GroundContinuumSuccIndex // β < i}, A i.val :=
      hUnbounded.trans (iInf_le _ β)
    apply (le_inf le_rfl hb).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    exact le_iSup_of_le i (bSet.mem_mk e w i.val)
  let g := weightedGraph e v w
  have hF : (⊤ : B) ≤ is_func g := by
    apply weightedGraph_func
    intro i j
    by_cases hij : i = j
    · subst j
      exact bv_refl
    · simp only [e,preparedOrdinalEntry_eq_bot_r416 hij,inf_bot_eq,bot_le]
  have hI : (⊤ : B) ≤ is_inj g := by
    apply weightedGraph_inj
    intro i j
    by_cases hij : i = j
    · subst j
      exact bv_refl
    · rw [show (w i ⊓ w j) ⊓ (v i =ᴮ v j) = ⊥ from hSeparated i j hij]
      exact bot_le
  have hR : (⊤ : B) ≤ is_total T R g := by
    apply weightedGraph_total_of_weighted_range e v w
    · intro y
      rw [show T = familyName e w from rfl,mem_familyName_r70]
    · exact hMembers
  have hinj : (⊤ : B) ≤ injects_into T R := le_iSup_of_le g (le_inf (le_inf hF hR) hI)
  exact unbounded_family_not_injects_small hB x hx T m hT
    (injects_into_trans (le_top.trans hinj) hSmall)

end JSP000930.Positive
