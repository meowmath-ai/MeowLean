import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace JSP000930.Positive.Dyadic

structure Interval where
  left : ℚ
  right : ℚ
  positive : left < right

def Interval.mid (s : Interval) : ℚ := (s.left + s.right) / 2

def Interval.width (s : Interval) : ℚ := s.right - s.left

theorem Interval.width_pos (s : Interval) : 0 < s.width :=
  sub_pos.mpr s.positive

def Interval.split (s : Interval) : Bool → Interval
  | false => ⟨s.left, s.mid, by unfold Interval.mid; linarith [s.positive]⟩
  | true => ⟨s.mid, s.right, by unfold Interval.mid; linarith [s.positive]⟩

theorem Interval.split_inside (s : Interval) (b : Bool) :
    s.left ≤ (s.split b).left ∧ (s.split b).right ≤ s.right := by
  cases b <;> simp only [Interval.split,Interval.mid] <;> constructor <;>
    linarith [s.positive]

theorem Interval.split_width (s : Interval) (b : Bool) :
    (s.split b).width = s.width * (1 / 2 : ℚ) := by
  cases b <;> simp only [Interval.split,Interval.width,Interval.mid] <;> ring

def Interval.follow (s : Interval) : List Bool → Interval
  | [] => s
  | b :: t => (s.split b).follow t
termination_by structural l => l

theorem Interval.follow_append (s : Interval) (u v : List Bool) :
    s.follow (u ++ v) = (s.follow u).follow v := by
  induction u generalizing s with
  | nil => simp [Interval.follow]
  | cons b t ih => simp only [List.cons_append,Interval.follow]; exact ih (s.split b)

theorem Interval.follow_width (s : Interval) (v : List Bool) :
    (s.follow v).width = s.width * (1 / 2 : ℚ) ^ v.length := by
  induction v generalizing s with
  | nil => simp [Interval.follow]
  | cons b t ih =>
    rw [Interval.follow,ih,Interval.split_width,List.length_cons,pow_succ]
    ring

theorem Interval.follow_inside (s : Interval) (v : List Bool) :
    s.left ≤ (s.follow v).left ∧ (s.follow v).right ≤ s.right := by
  induction v generalizing s with
  | nil => simp [Interval.follow]
  | cons b t ih =>
    simpa only [Interval.follow] using
      And.intro ((s.split_inside b).1.trans (ih (s.split b)).1)
        ((ih (s.split b)).2.trans (s.split_inside b).2)

def pointWord (q : ℚ) (s : Interval) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
    let b := if s.mid ≤ q then true else false
    b :: pointWord q (s.split b) n

theorem pointWord_length (q : ℚ) (s : Interval) (n : ℕ) :
    (pointWord q s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [pointWord,ih]

theorem pointWord_contains (q : ℚ) (s : Interval) (n : ℕ)
    (hl : s.left ≤ q) (hr : q ≤ s.right) :
    (s.follow (pointWord q s n)).left ≤ q ∧
      q ≤ (s.follow (pointWord q s n)).right := by
  induction n generalizing s with
  | zero => simpa [pointWord,Interval.follow] using And.intro hl hr
  | succ n ih =>
    by_cases H : s.mid ≤ q
    · simpa only [pointWord,ite_eq_left H,Interval.follow] using ih (s.split true) H hr
    · simpa only [pointWord,ite_eq_right H,Interval.follow] using
        ih (s.split false) hl (le_of_lt (lt_of_not_ge H))

theorem exists_descendant_inside (s : Interval) (a q b : ℚ)
    (ha : a < q) (hb : q < b) (hl : s.left ≤ q) (hr : q ≤ s.right) :
    ∃ v : List Bool, a < (s.follow v).left ∧ (s.follow v).right < b := by
  let ε := min (q-a) (b-q)
  have he : 0 < ε := lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one
    (div_pos he (s.width_pos)) (show (1 / 2 : ℚ) < 1 by norm_num)
  let v := pointWord q s n
  let t := s.follow v
  have hT : t.width < ε := by
    change (s.follow v).width < _
    rw [s.follow_width,pointWord_length]
    exact (mul_comm _ _).trans_lt ((lt_div_iff₀ s.width_pos).mp hn)
  obtain ⟨hL,hR⟩ := pointWord_contains q s n hl hr
  have hA : t.width < q-a := hT.trans_le (min_le_left _ _)
  have hB : t.width < b-q := hT.trans_le (min_le_right _ _)
  change t.left ≤ q at hL
  change q ≤ t.right at hR
  refine ⟨v, ?_⟩
  change a < t.left ∧ t.right < b
  unfold Interval.width at hA hB
  exact ⟨by linarith, by linarith⟩

def unitInterval : Interval := ⟨0,1,by norm_num⟩

end JSP000930.Positive.Dyadic
