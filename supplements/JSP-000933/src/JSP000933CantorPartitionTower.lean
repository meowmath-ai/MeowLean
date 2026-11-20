import JSP000933WordPartitionRefinement

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

def seedWordPartition (p : B) (s : Word) : IndexedPartition B Word p where
  weight u := if u=s then p else ⊥
  covers := by
    apply le_antisymm
    · apply iSup_le
      intro u
      by_cases h : u=s <;> simp [h]
    · have h := le_iSup (fun u : Word => if u=s then p else ⊥) s
      simpa only [ite_true] using h
  separate := by
    intro u v hne
    by_cases hu : u=s
    · have hv : v≠s := fun hv => hne (hu.trans hv.symm)
      simp [hu,hv]
    · simp [hu]

@[simp] theorem seedWordPartition_weight_r217 (p : B) (s : Word) :
    (seedWordPartition p s).weight s = p := by
  simp [seedWordPartition]

structure WordPartitionTower (B : Type) [CompleteBooleanAlgebra B] (p : B)
    (s : Word) (K : ℕ → Word → B) where
  level : ℕ → IndexedPartition B Word p
  seed : level 0 = seedWordPartition p s
  step : ∀ n, WordPartitionRefines (level n) (level (n+1))
  code : ∀ n w, (level (n+1)).weight w ≤ K n w
  lengthBound : ∀ n w, w.length < n → (level n).weight w = ⊥

theorem exists_wordPartitionTower_r217 (p : B) (s : Word) (K : ℕ → Word → B)
    (hK : ∀ n, DenseLongExtensions p (n+1) (K n)) :
    Nonempty (WordPartitionTower B p s K) := by
  classical
  let A (n : ℕ) (P : IndexedPartition B Word p) :=
    extend_wordPartition_r216 P (n+1) (K n) (hK n)
  let f : ℕ → IndexedPartition B Word p := Nat.rec (seedWordPartition p s) (fun n P => Classical.choose (A n P))
  have hF (n : ℕ) : WordPartitionRefines (f n) (f (n+1)) ∧
      (∀ w, (f (n+1)).weight w ≤ K n w) ∧
      (∀ w, w.length < n+1 → (f (n+1)).weight w = ⊥) :=
    Classical.choose_spec (A n (f n))
  refine ⟨⟨f,rfl,fun n => (hF n).1,fun n => (hF n).2.1,?_⟩⟩
  intro n w h
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ h)
  | succ n => exact (hF n).2.2 w h

theorem WordPartitionTower.refines_r217 {p : B} {s : Word} {K : ℕ → Word → B}
    (F : WordPartitionTower B p s K) {n m : ℕ} (h : n ≤ m) :
    WordPartitionRefines (F.level n) (F.level m) := by
  induction m with
  | zero =>
    have hn : n=0 := Nat.eq_zero_of_le_zero h
    subst n
    exact WordPartitionRefines.refl_r216 _
  | succ m ih =>
    by_cases hm : n = m+1
    · subst n
      exact WordPartitionRefines.refl_r216 _
    · have hn : n ≤ m := by omega
      exact WordPartitionRefines.trans_r216 (ih hn) (F.step m)

end CantorCodes
end JSP000933
