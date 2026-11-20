import JSP000933CantorClosedPotential

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

theorem merge_supported_wordRows_r223 {p : B} (P : IndexedPartition B Word p)
    (row : ∀ u : Word, IndexedPartition B Word (P.weight u))
    (hSupport : ∀ u v, (row u).weight v ≠ ⊥ → ExtendsWord u v) :
    ∃ Q : IndexedPartition B Word p, WordPartitionRefines P Q ∧
      (∀ v, Q.weight v = ⨆ u, (row u).weight v) := by
  classical
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
  refine ⟨⟨w,hCov,hSep⟩,?_,fun _ => rfl⟩
  intro u v hNon
  by_contra h
  apply hNon
  apply le_bot_iff.mp
  change P.weight u ⊓ (⨆ t : Word, (row t).weight v) ≤ ⊥
  rw [inf_iSup_eq]
  apply iSup_le
  intro t
  by_cases ht : t = u
  · subst t
    by_contra hz
    have hN : (row u).weight v ≠ ⊥ := fun he => hz (by rw [he,inf_bot_eq])
    exact h (hSupport u v hN)
  · exact (inf_le_inf_left _ ((row t).weight_le_r215 v)).trans
      (disjoint_iff_inf_le.mp (P.separate u t (Ne.symm ht)))

def IsChildWord (u v : Word) : Prop := v=u++[false] ∨ v=u++[true]

theorem extend_by_closedPotential_r223 {p : B} (P : IndexedPartition B Word p)
    (K : ℕ → Word → B) (n : ℕ)
    (hK : ∀ u, P.weight u ≤ closedPotential K u)
    (hLen : ∀ u, u.length < n → P.weight u = ⊥) :
    ∃ Q : IndexedPartition B Word p, WordPartitionRefines P Q ∧
      (∀ v, Q.weight v ≤ closedPotential K v) ∧ (∀ v, v.length < n+1 → Q.weight v = ⊥) := by
  classical
  let T (u v : Word) := if IsChildWord u v then closedPotential K v else ⊥
  have hRow (u : Word) : P.weight u ≤ ⨆ v, T u v := by
    apply (hK u).trans
    rw [closedPotential_binary_r222 K u]
    apply sup_le
    · exact (show closedPotential K (u++[false]) ≤ T u (u++[false]) by simp [T,IsChildWord]).trans
        (le_iSup (T u) (u++[false]))
    · exact (show closedPotential K (u++[true]) ≤ T u (u++[true]) by simp [T,IsChildWord]).trans
        (le_iSup (T u) (u++[true]))
  have he (u : Word) : ∃ R : IndexedPartition B Word (P.weight u), ∀ v, R.weight v ≤ T u v :=
    exists_indexedPartition_of_join_r215 (P.weight u) (T u) (hRow u)
  choose row hRowTest using he
  have hChild (u v : Word) (hp : (row u).weight v ≠ ⊥) : IsChildWord u v := by
    by_contra hn
    exact hp (le_bot_iff.mp ((hRowTest u v).trans_eq (ite_eq_right hn)))
  have hSupp (u v : Word) (hp : (row u).weight v ≠ ⊥) : ExtendsWord u v := by
    rcases hChild u v hp with rfl | rfl
    · exact wordExtends_appendBit_r221 u false
    · exact wordExtends_appendBit_r221 u true
  obtain ⟨Q,hQ,hFormula⟩ := merge_supported_wordRows_r223 P row hSupp
  refine ⟨Q,hQ,?_,?_⟩
  · intro v
    rw [hFormula]
    apply iSup_le
    intro u
    apply (hRowTest u v).trans
    by_cases h : IsChildWord u v <;> simp [T,h]
  · intro v hv
    rw [hFormula]
    apply le_bot_iff.mp
    apply iSup_le
    intro u
    by_contra hn
    have hN : (row u).weight v ≠ ⊥ := fun h => hn h.le
    have hLv : v.length = u.length+1 := by
      rcases hChild u v hN with rfl | rfl <;> simp
    have hLu : u.length<n := by omega
    exact hn (((row u).weight_le_r215 v).trans_eq (hLen u hLu))

end CantorCodes
end JSP000933
