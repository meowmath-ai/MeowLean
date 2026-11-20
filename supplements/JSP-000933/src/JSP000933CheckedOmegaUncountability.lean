import JSP000933CountableChoiceProfiles
import Flypitch4.Zfc

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

theorem checkedDistinct_eq_bot_r412 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (y : PSet.{0}) (hY : ∀ i j : y.Type,i≠j → ¬PSet.Equiv (y.Func i) (y.Func j))
    {i j : y.Type} (h : i≠j) :
    ((check (y.Func i) : bSet B) =ᴮ check (y.Func j))=⊥ :=
  check_bv_eq_bot_of_not_equiv (hY i j h)

theorem checkNatRows_total_r412 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (y : PSet.{0}) (G : bSet B) (m : B)
    (hG : m≤ is_func' bSet.omega (check y) G) (n : ℕ) :
    m≤⨆ j : y.Type,pair (check (PSet.omega.Func (ULift.up n))) (check (y.Func j))∈ᴮ G := by
  let w : (bSet.omega : bSet B).type := (ULift.up n : ULift.{0} ℕ)
  have hT := (is_total_iff_is_total'.mp (is_total_of_is_func' hG)).trans (iInf_le _ w)
  change m≤(bSet.omega : bSet B).bval w ⟹
    (⨆ j : (check y : bSet B).type,(check y : bSet B).bval j⊓
      (pair ((bSet.omega : bSet B).func w) ((check y : bSet B).func j)∈ᴮ G)) at hT
  rw [← deduction] at hT
  have hwVal : (bSet.omega : bSet B).bval w = ⊤ := rfl
  have hwFunc : (bSet.omega : bSet B).func w = check (PSet.omega.Func (ULift.up n)) := rfl
  rw [hwVal,inf_top_eq] at hT
  simp only [hwFunc,check_bval_top,top_inf_eq,check_func] at hT
  apply hT.trans
  apply iSup_le
  intro j
  exact le_iSup (fun i : y.Type => pair (check (PSet.omega.Func (ULift.up n))) (check (y.Func i)) ∈ᴮ G)
    (check_cast j)

theorem countablyClosed_checked_noOmegaSurj_r412 {P : Type} [Preorder P] [Nonempty P]
    (hP : IsCountablyClosed P) (y : PSet.{0})
    (hY : ∀ i j : y.Type,i≠j → ¬PSet.Equiv (y.Func i) (y.Func j))
    (hCard : ℵ₀<Cardinal.mk y.Type) :
    (surjects_onto bSet.omega (check y) : RO P)=⊥ := by
  classical
  let B := RO P
  apply le_bot_iff.mp
  unfold surjects_onto
  apply iSup_le
  intro G
  let m : B := is_surj_onto bSet.omega (check y) G
  change m≤⊥
  by_contra hn
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 m (fun he => hn he.le)
  let V (n : ℕ) (j : y.Type) : B :=
    (pair (check (PSet.omega.Func (ULift.up n))) (check (y.Func j))∈ᴮ G)
  have hRow (n : ℕ) : imageCondition p≤⨆ j,V n j :=
    checkNatRows_total_r412 y G (imageCondition p) (hp.trans inf_le_left) n
  obtain ⟨q,f,hq,hF⟩ := exists_allChoiceProfiles_r411 hP p V hRow
  have hQ := (imageCondition_mono_r50 hq).trans hp
  have hNS : ¬Function.Surjective f := by
    intro h
    exact hCard.not_ge ((Cardinal.mk_le_of_surjective h).trans_eq Cardinal.mk_nat)
  have hAway : ∃ j : y.Type,∀ n,f n≠j := by
    by_contra hn'
    apply hNS
    intro j
    by_contra hj'
    exact hn' ⟨j,fun n heq => hj' ⟨n,heq⟩⟩
  obtain ⟨j,hj⟩ := hAway
  let a : bSet B := check (y.Func j)
  have ha : imageCondition q≤a∈ᴮ (check y : bSet B) := check_mem (PSet.func_mem y j)
  have he : imageCondition q≤⨆ z : bSet B,z∈ᴮ bSet.omega⊓(pair z a∈ᴮ G) :=
    (le_inf ((hQ.trans inf_le_right).trans (iInf_le _ a)) ha).trans Lattice.bv_imp_elim
  rw [← bounded_exists (h_congr := show B_ext (fun z : bSet B => pair z a∈ᴮ G) from
    B_ext_pair_mem_left)] at he
  have hBot : imageCondition q≤⊥ := by
    apply (le_inf le_rfl he).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    simp only [bSet.omega,check_bval_top,top_inf_eq,check_func]
    let k : ℕ := (check_cast n : PSet.omega.Type).down
    let N : B := imageCondition q⊓V k j
    have h1 : N≤ is_func G := inf_le_left.trans (hQ.trans
      (inf_le_left.trans inf_le_left))
    have h2 : N≤V k (f k) := inf_le_left.trans (hF k)
    have h3 : N≤V k j := inf_le_right
    exact (eq_of_is_func_of_eq h1 bv_refl h2 h3).trans_eq
      (checkedDistinct_eq_bot_r412 y hY (hj k))
  exact imageCondition_ne_bot_r50 q (le_bot_iff.mp hBot)

end PreparedModel
end JSP000933
