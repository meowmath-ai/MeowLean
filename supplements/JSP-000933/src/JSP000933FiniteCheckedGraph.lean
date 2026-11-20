import JSP000933CouplingOrderTransfer
import JSP000933BooleanSentenceLanguage

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace PositiveForcing

open BooleanNames

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedNat_eq_crisp_r189 (i j : ℕ) :
    (bSet.of_nat i =ᴮ (bSet.of_nat j : bSet B)) = crispTruth B (i = j) := by
  classical
  by_cases h : i = j
  · subst j
    exact (top_unique bSet.bv_refl).trans (by simp [crispTruth])
  · exact (checkedNat_eq_bot_r174 h).trans (by simp [crispTruth,h])

theorem pair_eq_inf_r189 (x y u v : bSet B) :
    (bSet.pair x y =ᴮ bSet.pair u v) = ((x =ᴮ u) ⊓ (y =ᴮ v)) := by
  apply le_antisymm
  · exact le_inf bSet.eq_of_eq_pair_left bSet.eq_of_eq_pair_right
  · exact bSet.pair_congr inf_le_left inf_le_right

noncomputable def valueAtNat (G : bSet B) (i j : ℕ) : B :=
  bSet.pair (bSet.of_nat i) (bSet.of_nat j) ∈ᴮ G

def checkedFiniteGraph {m : ℕ} (f : Fin m → ℕ) : bSet B :=
  familyName (fun i => bSet.pair (bSet.of_nat i.val) (bSet.of_nat (f i))) (fun _ => ⊤)

theorem checkedFiniteGraph_value_r189 {m : ℕ} (f : Fin m → ℕ) (i j : ℕ) :
    valueAtNat (checkedFiniteGraph (B := B) f) i j =
      crispTruth B (∃ k : Fin m, k.val = i ∧ f k = j) := by
  classical
  unfold valueAtNat checkedFiniteGraph
  rw [mem_familyName_r70]
  simp only [top_inf_eq,pair_eq_inf_r189,checkedNat_eq_crisp_r189]
  by_cases h : ∃ k : Fin m, k.val = i ∧ f k = j
  · obtain ⟨k,hk,hf⟩ := h
    have he := (le_iSup
      (fun k : Fin m => crispTruth B (i = k.val) ⊓ crispTruth B (j = f k)) k)
    rw [show crispTruth B (i = k.val) = ⊤ by simp [crispTruth,hk.symm],
        show crispTruth B (j = f k) = ⊤ by simp [crispTruth,hf.symm],inf_top_eq] at he
    exact (top_unique he).trans (by simp [crispTruth,show ∃ k : Fin m, k.val = i ∧ f k = j from ⟨k,hk,hf⟩])
  · have he : (⨆ k : Fin m, crispTruth B (i = k.val) ⊓ crispTruth B (j = f k)) = ⊥ := by
      apply le_bot_iff.mp
      apply iSup_le
      intro k
      by_cases hk : i = k.val
      · have hj : j ≠ f k := fun hj => h ⟨k,hk.symm,hj.symm⟩
        simp [crispTruth,hj]
      · simp [crispTruth,hk]
    exact he.trans (by simp [crispTruth,h])

theorem checkedFiniteGraph_value_at_index_r189 {m : ℕ} (f : Fin m → ℕ) (i : Fin m) (j : ℕ) :
    valueAtNat (checkedFiniteGraph (B := B) f) i.val j = crispTruth B (f i = j) := by
  rw [checkedFiniteGraph_value_r189]
  apply crispTruth_propext_r188
  constructor
  · rintro ⟨k,hk,hf⟩
    exact (Fin.ext hk) ▸ hf
  · intro hj
    exact ⟨i,rfl,hj⟩

end PositiveForcing
end JSP000933
