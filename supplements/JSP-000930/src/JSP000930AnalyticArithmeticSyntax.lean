import JSP000933SetSentence

open Fol JSP000933.SetLanguage

namespace JSP000930.AnalyticSyntax

def naturalPow_f {n : ℕ} (x m r : STerm n) : SForm n :=
  exIn omega fun one =>
    bd_and (successor_f zero one)
      (naturalRecursion_f (up m) one (up r) (fun _ : Fin 1 => up x)
        (fun p _ cur next => multiplication_f cur (p 0) next))

def unpackRational_f {n k : ℕ} (q : STerm n) (par : Fin k → STerm n)
    (body : ∀ {l : ℕ}, (Fin k → STerm l) → STerm l → STerm l → STerm l → SForm l) :
    SForm n :=
  exIn omega fun a =>
    exIn omega fun b =>
      exIn omega fun d =>
        bd_and (bd_not (bd_equal d zero))
          (bd_and (bd_equal (up3 q) (pair' (up2 a) (pair' (up b) d)))
            (body (fun i => up3 (par i)) (up2 a) (up b) d))

inductive NatExpr (k : ℕ) where
  | var (i : Fin k)
  | add (a b : NatExpr k)
  | mul (a b : NatExpr k)
  | pow (a b : NatExpr k)

def NatExpr.val {k : ℕ} (e : NatExpr k) (p : Fin k → ℕ) : ℕ :=
  match e with
  | .var i => p i
  | .add a b => a.val p + b.val p
  | .mul a b => a.val p * b.val p
  | .pow a b => a.val p ^ b.val p

abbrev NatOpF := ∀ {d : ℕ}, STerm d → STerm d → STerm d → SForm d

def natRelBinary_f {n : ℕ} (op : NatOpF)
    (relA relB : ∀ {d : ℕ}, (STerm n → STerm d) → STerm d → SForm d)
    (out : STerm n) : SForm n :=
  exIn omega fun a =>
    exIn omega fun b =>
      bd_and (relA up2 (up a))
        (bd_and (relB up2 b) (op (up a) b (up2 out)))

def NatExpr.rel_f {n k : ℕ} (e : NatExpr k) (p : Fin k → STerm n)
    (out : STerm n) : SForm n :=
  match e with
  | .var i => bd_equal out (p i)
  | .add a b => natRelBinary_f addition_f
      (fun lift t => a.rel_f (fun i => lift (p i)) t)
      (fun lift t => b.rel_f (fun i => lift (p i)) t) out
  | .mul a b => natRelBinary_f multiplication_f
      (fun lift t => a.rel_f (fun i => lift (p i)) t)
      (fun lift t => b.rel_f (fun i => lift (p i)) t) out
  | .pow a b => natRelBinary_f naturalPow_f
      (fun lift t => a.rel_f (fun i => lift (p i)) t)
      (fun lift t => b.rel_f (fun i => lift (p i)) t) out
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals omega

def NatExpr.compare_f {n k : ℕ} (cmp : ∀ {d : ℕ}, STerm d → STerm d → SForm d)
    (e f : NatExpr k) (p : Fin k → STerm n) : SForm n :=
  exIn omega fun x => exIn omega fun y =>
    bd_and (e.rel_f (fun i => up2 (p i)) (up x))
      (bd_and (f.rel_f (fun i => up2 (p i)) y) (cmp (up x) y))

def crossOrder_f {n : ℕ} (a b d e f g : STerm n) : SForm n :=
  let L : NatExpr 6 := .add (.mul (.var 0) (.var 5)) (.mul (.var 4) (.var 2))
  let R : NatExpr 6 := .add (.mul (.var 3) (.var 2)) (.mul (.var 1) (.var 5))
  L.compare_f natLE_f R (fun i => ![a,b,d,e,f,g] i)

def rationalTernary_f {n : ℕ} (x y z : STerm n)
    (body : ∀ {d : ℕ}, (Fin 9 → STerm d) → SForm d) : SForm n :=
  unpackRational_f x (fun i => ![y,z] i) (fun tail a b d =>
    unpackRational_f (tail 0) (fun i => ![a,b,d,tail 1] i) (fun px e f g =>
      unpackRational_f (px 3) (fun i => ![px 0,px 1,px 2,e,f,g] i)
        (fun py h j k => body (fun i => ![py 0,py 1,py 2,py 3,py 4,py 5,h,j,k] i))))

def crossAdd_f {d : ℕ} (q : Fin 9 → STerm d) : SForm d :=
  let I (i : Fin 9) : NatExpr 9 := .var i
  let p := NatExpr.add (.mul (I 0) (I 5)) (.mul (I 3) (I 2))
  let m := NatExpr.add (.mul (I 1) (I 5)) (.mul (I 4) (I 2))
  let den := NatExpr.mul (I 2) (I 5)
  let L := NatExpr.add (.mul p (I 8)) (.mul (I 7) den)
  let R := NatExpr.add (.mul (I 6) den) (.mul m (I 8))
  L.compare_f bd_equal R q

def crossMul_f {d : ℕ} (q : Fin 9 → STerm d) : SForm d :=
  let I (i : Fin 9) : NatExpr 9 := .var i
  let p := NatExpr.add (.mul (I 0) (I 3)) (.mul (I 1) (I 4))
  let m := NatExpr.add (.mul (I 0) (I 4)) (.mul (I 1) (I 3))
  let den := NatExpr.mul (I 2) (I 5)
  let L := NatExpr.add (.mul p (I 8)) (.mul (I 7) den)
  let R := NatExpr.add (.mul (I 6) den) (.mul m (I 8))
  L.compare_f bd_equal R q

end JSP000930.AnalyticSyntax
