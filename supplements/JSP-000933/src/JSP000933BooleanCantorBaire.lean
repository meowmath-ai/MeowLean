import JSP000933CantorPartitionTower

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

def trueWordAt (k : ℕ) (u : Word) : Prop :=
  ∃ hk : k < u.length, u[k]'hk = true

noncomputable def WordPartitionTower.limitBits {p : B} {s : Word} {K : ℕ → Word → B}
    (F : WordPartitionTower B p s K) : ℕ → B :=
  fun k => ⨆ v : {v : Word // trueWordAt k v}, (F.level (k+1)).weight v.1

theorem WordPartitionTower.overlap_agrees_r218 {p : B} {s : Word} {K : ℕ → Word → B}
    (F : WordPartitionTower B p s K) (n m : ℕ) (u v : Word) (k : ℕ)
    (hu : k < u.length) (hv : k < v.length)
    (h : (F.level n).weight u ⊓ (F.level m).weight v ≠ ⊥) :
    u[k]'hu = v[k]'hv := by
  rcases le_total n m with hn | hm
  · obtain ⟨_,he⟩ := (F.refines_r217 hn) u v h
    exact he ⟨k,hu⟩
  · have hh : (F.level m).weight v ⊓ (F.level n).weight u ≠ ⊥ := by simpa only [inf_comm] using h
    obtain ⟨_,he⟩ := (F.refines_r217 hm) v u hh
    exact (he ⟨k,hv⟩).symm

theorem WordPartitionTower.weight_le_limitLiteral_r218 {p : B} {s : Word} {K : ℕ → Word → B}
    (F : WordPartitionTower B p s K) (n : ℕ) (u : Word) (k : ℕ) (hu : k < u.length) :
    (F.level n).weight u ≤ literal (F.limitBits k) (u[k]'hu) := by
  classical
  let a := (F.level n).weight u
  cases hb : u[k]'hu
  · change a ≤ (F.limitBits k)ᶜ
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    unfold WordPartitionTower.limitBits
    rw [inf_iSup_eq]
    apply iSup_le
    intro v
    by_contra hn
    obtain ⟨hk,hK⟩ := v.2
    have h := F.overlap_agrees_r218 n (k+1) u v.1 k hu hk
      (fun he => hn he.le)
    rw [hb,hK] at h
    cases h
  · change a ≤ F.limitBits k
    have ha : a ≤ p := (F.level n).weight_le_r215 u
    calc
      a = a ⊓ (⨆ v : Word, (F.level (k+1)).weight v) := by
        rw [(F.level (k+1)).covers,inf_eq_left.mpr ha]
      _ ≤ F.limitBits k := by
        rw [inf_iSup_eq]
        apply iSup_le
        intro v
        by_cases h : a ⊓ (F.level (k+1)).weight v = ⊥
        · exact h.le.trans bot_le
        · have hv : k < v.length := by
            by_contra hh
            have he : (F.level (k+1)).weight v = ⊥ :=
              F.lengthBound (k+1) v (by omega)
            exact h (by rw [he,inf_bot_eq])
          have he := F.overlap_agrees_r218 n (k+1) u v k hu hv h
          let j : {v : Word // trueWordAt k v} := ⟨v,hv,he.symm.trans hb⟩
          exact inf_le_right.trans (le_iSup (fun t : {v : Word // trueWordAt k v} =>
            (F.level (k+1)).weight t.1) j)

theorem WordPartitionTower.weight_le_limitCylinder_r218 {p : B} {s : Word} {K : ℕ → Word → B}
    (F : WordPartitionTower B p s K) (n : ℕ) (u : Word) :
    (F.level n).weight u ≤ cylinderValue F.limitBits u := by
  apply le_iInf
  intro i
  exact F.weight_le_limitLiteral_r218 n u i.val i.isLt

theorem exists_namedReal_meeting_denseCodes_r218 (p : B) (s : Word) (K : ℕ → Word → B)
    (hK : ∀ n, DenseLongExtensions p (n+1) (K n)) :
    ∃ x : ℕ → B, p ≤ cylinderValue x s ∧ ∀ n, p ≤ openValue (K n) x := by
  obtain ⟨F⟩ := exists_wordPartitionTower_r217 p s K hK
  refine ⟨F.limitBits,?_,?_⟩
  · have h := F.weight_le_limitCylinder_r218 0 s
    simpa only [F.seed,seedWordPartition_weight_r217] using h
  · intro n
    apply (F.level (n+1)).covers.ge.trans
    apply iSup_le
    intro u
    exact le_iSup_of_le u (le_inf (F.code n u) (F.weight_le_limitCylinder_r218 (n+1) u))

end CantorCodes
end JSP000933
