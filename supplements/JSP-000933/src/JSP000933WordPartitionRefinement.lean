import JSP000933IndexedBooleanPartitions
import JSP000933OffDiagonalTable

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

theorem extendsWord_refl_r216 (w : Word) : ExtendsWord w w :=
  ⟨le_rfl,fun _ => rfl⟩

theorem extendsWord_trans_r216 {s t u : Word} (h₁ : ExtendsWord s t) (h₂ : ExtendsWord t u) :
    ExtendsWord s u := by
  obtain ⟨l₁,e₁⟩ := h₁
  obtain ⟨l₂,e₂⟩ := h₂
  refine ⟨l₁.trans l₂,fun i => ?_⟩
  exact (e₁ i).trans (e₂ ⟨i.val,i.isLt.trans_le l₁⟩)

def WordPartitionRefines {p : B} (P Q : IndexedPartition B Word p) : Prop :=
  ∀ u v, P.weight u ⊓ Q.weight v ≠ ⊥ → ExtendsWord u v

theorem WordPartitionRefines.refl_r216 {p : B} (P : IndexedPartition B Word p) :
    WordPartitionRefines P P := by
  intro u v h
  by_cases he : u=v
  · subst v; exact extendsWord_refl_r216 u
  · exact False.elim (h (le_bot_iff.mp (disjoint_iff_inf_le.mp (P.separate u v he))))

theorem WordPartitionRefines.trans_r216 {p : B} {P Q R : IndexedPartition B Word p}
    (hpq : WordPartitionRefines P Q) (hqr : WordPartitionRefines Q R) :
    WordPartitionRefines P R := by
  intro u w hw
  let c := P.weight u ⊓ R.weight w
  have hq : c ≤ ⨆ v, Q.weight v :=
    (inf_le_left.trans (P.weight_le_r215 u)).trans_eq Q.covers.symm
  obtain ⟨v,q,hN,hqc,hqv⟩ := exists_nonzero_below_choice_r135 c hw Q.weight hq
  have huv : P.weight u ⊓ Q.weight v ≠ ⊥ := by
    intro h
    exact hN (le_bot_iff.mp ((le_inf (hqc.trans inf_le_left) hqv).trans_eq h))
  have hvw : Q.weight v ⊓ R.weight w ≠ ⊥ := by
    intro h
    exact hN (le_bot_iff.mp ((le_inf hqv (hqc.trans inf_le_right)).trans_eq h))
  exact extendsWord_trans_r216 (hpq u v huv) (hqr v w hvw)

def DenseLongExtensions (p : B) (n : ℕ) (K : Word → B) : Prop :=
  ∀ u : Word, p ≤ ⨆ v : {v : Word // ExtendsWord u v ∧ n ≤ v.length}, K v.1

theorem extend_wordPartition_r216 {p : B} (P : IndexedPartition B Word p) (n : ℕ) (K : Word → B)
    (hK : DenseLongExtensions p n K) :
    ∃ Q : IndexedPartition B Word p, WordPartitionRefines P Q ∧
      (∀ v, Q.weight v ≤ K v) ∧ (∀ v, v.length < n → Q.weight v = ⊥) := by
  classical
  let allowed (u v : Word) := ExtendsWord u v ∧ n ≤ v.length
  let T (u v : Word) : B := if allowed u v then K v else ⊥
  have hT (u : Word) : P.weight u ≤ ⨆ v, T u v := by
    apply ((P.weight_le_r215 u).trans (hK u)).trans
    apply iSup_le
    intro v
    exact (show K v.1 ≤ T u v.1 by simp [T,allowed,v.2]).trans (le_iSup (T u) v.1)
  have hChoose (u : Word) :
      ∃ Q : IndexedPartition B Word (P.weight u), ∀ v, Q.weight v ≤ T u v :=
    exists_indexedPartition_of_join_r215 (P.weight u) (T u) (hT u)
  choose row hRow using hChoose
  let w (v : Word) := ⨆ u : Word, (row u).weight v
  have hCov : (⨆ v, w v) = p := by
    unfold w
    rw [iSup_comm]
    have he : (fun u : Word => ⨆ v, (row u).weight v) = P.weight :=
      funext (fun u => (row u).covers)
    rw [he,P.covers]
  have hSep (v v' : Word) (hne : v ≠ v') : Disjoint (w v) (w v') := by
    apply disjoint_iff_inf_le.mpr
    change (⨆ u : Word, (row u).weight v) ⊓ (⨆ u : Word, (row u).weight v') ≤ ⊥
    rw [iSup_inf_iSup]
    apply iSup_le
    intro uv
    by_cases he : uv.1 = uv.2
    · rw [← he]
      exact disjoint_iff_inf_le.mp ((row uv.1).separate v v' hne)
    · exact (inf_le_inf ((row uv.1).weight_le_r215 v) ((row uv.2).weight_le_r215 v')).trans
        (disjoint_iff_inf_le.mp (P.separate uv.1 uv.2 he))
  refine ⟨⟨w,hCov,hSep⟩,?_,?_,?_⟩
  · intro u v hNon
    by_contra h
    apply hNon
    apply le_bot_iff.mp
    change P.weight u ⊓ (⨆ t : Word, (row t).weight v) ≤ ⊥
    rw [inf_iSup_eq]
    apply iSup_le
    intro t
    by_cases ht : t = u
    · subst t
      have hA : ¬ allowed u v := fun h' => h h'.1
      exact inf_le_right.trans ((hRow u v).trans_eq (ite_eq_right hA))
    · exact (inf_le_inf_left _ ((row t).weight_le_r215 v)).trans
        (disjoint_iff_inf_le.mp (P.separate u t (Ne.symm ht)))
  · intro v
    apply iSup_le
    intro u
    apply (hRow u v).trans
    by_cases h : allowed u v <;> simp [T,h]
  · intro v hv
    apply le_bot_iff.mp
    apply iSup_le
    intro u
    have hA : ¬ allowed u v := fun h => (not_le_of_gt hv) h.2
    exact (hRow u v).trans_eq (ite_eq_right hA)

end CantorCodes
end JSP000933
