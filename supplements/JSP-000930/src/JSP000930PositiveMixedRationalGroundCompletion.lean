import JSP000930PositiveLocalRationalCutEnclosures
import Mathlib.Data.Real.Basic

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B] [Countable J] [Nonempty J]

def narrowRationalPair (n : ℕ) :=
  {qr : RatPresentation × RatPresentation //
    qr.1.value < qr.2.value ∧ qr.2.value-qr.1.value < (1/2 : ℚ)^n}

noncomputable def cutCoordSchedule : ℕ → J × ℕ := by
  letI := Encodable.ofCountable (J × ℕ)
  exact fun n => (Encodable.decode (α := J × ℕ) n).getD (Classical.choice inferInstance,0)

noncomputable def cutCoordIndex (j : J) (n : ℕ) : ℕ := by
  letI := Encodable.ofCountable (J × ℕ)
  exact Encodable.encode (j,n)

theorem cutCoordSchedule_hits (j : J) (n : ℕ) :
    cutCoordSchedule (cutCoordIndex j n) = (j,n) := by
  letI := Encodable.ofCountable (J × ℕ)
  unfold cutCoordSchedule cutCoordIndex
  rw [Encodable.encodek] <;> rfl

theorem mixed_cut_ground_completion {X : ℕ → Type}
    (β : J → RatPresentation → B) (m : B) (hm : m ≠ ⊥)
    (hβ : ∀ j, ProperCutOn m (β j))
    (V : ∀ n,X n → B) (hV : ∀ n,m ≤ ⨆ x,V n x) :
    ∃ (p : ℕ → B) (select : ∀ n,X n) (z : J → ℝ)
      (box : ∀ j : J,∀ n : ℕ,narrowRationalPair n),
      Antitone p ∧ (∀ n,p n ≠ ⊥) ∧ (∀ n,p n ≤ m) ∧
      (∀ n,p n ≤ V n (select n)) ∧
      ∀ j n,
        RationalEncloses (β j) (box j n).val.1 (box j n).val.2 (p (cutCoordIndex j n)) ∧
          ((box j n).val.1.value : ℝ) ≤ z j ∧ z j ≤ ((box j n).val.2.value : ℝ) := by
  classical
  let W (k : ℕ) (c : narrowRationalPair (cutCoordSchedule (J := J) k).2 × X k) : B :=
    (β (cutCoordSchedule (J := J) k).1 c.1.val.1 ⊓
      (β (cutCoordSchedule (J := J) k).1 c.1.val.2)ᶜ) ⊓ V k c.2
  have hW (k : ℕ) : m ≤ ⨆ c,W k c := by
    have hε : 0 < (1/2 : ℚ) ^ (cutCoordSchedule (J := J) k).2 := by positivity
    have hR := rational_enclosure_dense (hβ (cutCoordSchedule (J := J) k).1) _ hε
    refine (le_inf hR (hV k)).trans ?_
    rw [iSup_inf_iSup]
    exact iSup_le fun c => le_iSup (W k) c
  obtain ⟨p,f,hAnti,hNZ,hM,hF⟩ := descending_nonzero_cover_choices W m hm hW
  let box (j : J) (n : ℕ) : narrowRationalPair n :=
    cast (congrArg (fun t : J × ℕ => narrowRationalPair t.2)
      (cutCoordSchedule_hits j n)) (f (cutCoordIndex j n)).1
  have box_encloses (j : J) (n : ℕ) :
      RationalEncloses (β j) (box j n).val.1 (box j n).val.2 (p (cutCoordIndex j n)) := by
    let k := cutCoordIndex j n
    let a := cutCoordSchedule (J := J) k
    have ha : a = (j,n) := cutCoordSchedule_hits j n
    have hv := (hF k).trans inf_le_left
    change p k ≤ β a.1 (f k).1.val.1 ⊓ (β a.1 (f k).1.val.2)ᶜ at hv
    have helper (a : J × ℕ) (c : narrowRationalPair a.2) (ha : a = (j,n))
        (v : B) (h : v ≤ β a.1 c.val.1 ⊓ (β a.1 c.val.2)ᶜ) :
        RationalEncloses (β j) (cast (congrArg (fun t : J × ℕ => narrowRationalPair t.2) ha) c).val.1
          (cast (congrArg (fun t : J × ℕ => narrowRationalPair t.2) ha) c).val.2 v := by
      subst a
      exact ⟨h.trans inf_le_left,h.trans inf_le_right⟩
    exact helper a (f k).1 ha (p k) hv
  have overlap (j : J) (a b : ℕ) : (box j a).val.1.value < (box j b).val.2.value := by
    let k := max (cutCoordIndex j a) (cutCoordIndex j b)
    have hlo := (hAnti (le_max_left (cutCoordIndex j a) (cutCoordIndex j b))).trans (box_encloses j a).1
    have hhi := (hAnti (le_max_right (cutCoordIndex j a) (cutCoordIndex j b))).trans (box_encloses j b).2
    exact enclosure_positive_width (hβ j) (hM k) (hNZ k) ⟨hlo,hhi⟩
  let z (j : J) : ℝ := sSup (Set.range (fun a : ℕ => ((box j a).val.1.value : ℝ)))
  have hLower (j : J) (n : ℕ) : ((box j n).val.1.value : ℝ) ≤ z j := by
    apply le_csSup
    · use ((box j 0).val.2.value : ℝ)
      rintro _ ⟨k,rfl⟩
      exact Rat.cast_le.mpr (overlap j k 0).le
    · exact Set.mem_range_self n
  have hUpper (j : J) (n : ℕ) : z j ≤ ((box j n).val.2.value : ℝ) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨k,rfl⟩
    exact Rat.cast_le.mpr (overlap j k n).le
  exact ⟨p,fun n => (f n).2,z,box,hAnti,hNZ,hM,
    fun n => (hF n).trans inf_le_right,
    fun j n => ⟨box_encloses j n,hLower j n,hUpper j n⟩⟩

end JSP000930.Positive
