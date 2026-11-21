import JSP000930PositiveSubmodelTaylorNameTransport

namespace JSP000930.Positive

open JSP000933.CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

theorem descending_nonzero_cover_choices
    {X : ℕ → Type} (W : ∀ n,X n → B) (m : B) (hm : m ≠ ⊥)
    (hc : ∀ n,m ≤ ⨆ j,W n j) :
    ∃ b : ℕ → B, ∃ e : ∀ n,X n,
      Antitone b ∧ (∀ n,b n ≠ ⊥) ∧ (∀ n,b n ≤ m) ∧ ∀ n,b n ≤ W n (e n) := by
  classical
  let Mark := {x : B // x ≠ ⊥ ∧ x ≤ m}
  have hStep (n : ℕ) (p : Mark) :
      ∃ ep : X n × Mark, ep.2.val ≤ p.val ∧ ep.2.val ≤ W n ep.1 := by
    have hi : p.val ≤ ⨆ j,W n j := p.property.2.trans (hc n)
    obtain ⟨j,q,hq,hqp,hqW⟩ :=
      exists_nonzero_below_choice_r135 p.val p.property.1 (W n) hi
    exact ⟨(j,⟨q,hq,hqp.trans p.property.2⟩),hqp,hqW⟩
  let step (n : ℕ) (p : Mark) := Classical.choose (hStep n p)
  have hNext (n : ℕ) (p : Mark) : (step n p).2.val ≤ p.val :=
    (Classical.choose_spec (hStep n p)).1
  have hChoice (n : ℕ) (p : Mark) : (step n p).2.val ≤ W n (step n p).1 :=
    (Classical.choose_spec (hStep n p)).2
  let init : Mark := ⟨m,hm,le_rfl⟩
  let state : ℕ → Mark := Nat.rec init (fun n p => (step n p).2)
  let b (n : ℕ) := (state (n+1)).val
  let e (n : ℕ) := (step n (state n)).1
  have hS (n : ℕ) : state (n+1) = (step n (state n)).2 := rfl
  have hA : Antitone b := by
    apply antitone_nat_of_succ_le
    intro n
    change (state (n+1+1)).val ≤ (state (n+1)).val
    rw [hS (n+1)]
    exact hNext (n+1) (state (n+1))
  refine ⟨b,e,hA,fun n => (state (n+1)).property.1,
    fun n => (state (n+1)).property.2,fun n => ?_⟩
  change (state (n+1)).val ≤ W n (step n (state n)).1
  rw [hS n]
  exact hChoice n (state n)

theorem positive_finite_certificate_of_local_choices
    {X : ℕ → Type} {C : Type} (W : ∀ n,X n → B) (V : C → B)
    (m : B) (hm : m ≠ ⊥) (hc : ∀ n,m ≤ ⨆ j,W n j)
    (solve : ∀ f : (∀ n,X n),
      (∀ k : ℕ, ∃ p : B,p ≠ ⊥ ∧ p ≤ m ∧ ∀ n : Fin (k+1),p ≤ W n.val (f n.val)) →
      ∃ (k : ℕ) (c : C), (m ⊓ (⨅ n : Fin (k+1),W n.val (f n.val))) ≤ V c) :
    ∃ (c : C) (p : B),p ≠ ⊥ ∧ p ≤ m ∧ p ≤ V c := by
  obtain ⟨b,f,hb,hNZ,hbm,hW⟩ := descending_nonzero_cover_choices W m hm hc
  have hLocal (k : ℕ) : ∃ p : B,p ≠ ⊥ ∧ p ≤ m ∧
      ∀ n : Fin (k+1),p ≤ W n.val (f n.val) := by
    refine ⟨b k,hNZ k,hbm k,fun n => ?_⟩
    exact (hb (Nat.le_of_lt_succ n.isLt)).trans (hW n.val)
  obtain ⟨k,c,hc⟩ := solve f hLocal
  exact ⟨c,b k,hNZ k,hbm k,(le_inf (hbm k)
    (le_iInf fun n : Fin (k+1) => (hb (Nat.le_of_lt_succ n.isLt)).trans (hW n.val))).trans hc⟩

end JSP000930.Positive
