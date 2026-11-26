import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

noncomputable section

namespace SparseCubes.Certificate

/-- An outer coefficient list is in ascending powers. The innermost coefficients are integers. -/
abbrev Tower : Nat → Type
  | 0 => Int
  | n+1 => List (Tower n)

def value {α : Type} (f : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | h :: t => f h + x * value f x t

def interp : (n : Nat) → Tower n → (Nat → ℝ) → ℝ
  | 0, z, _ => (z : ℝ)
  | n+1, z, v => value (fun a => interp n a (fun k => v (k+1))) (v 0) z

def plusList {α : Type} (plus : α → α → α) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => plus x y :: plusList plus xs ys

theorem value_plusList {α : Type} (f : α → ℝ) (x : ℝ) (plus : α → α → α)
    (h : ∀ a b, f (plus a b) = f a + f b) (xs ys : List α) :
    value f x (plusList plus xs ys) = value f x xs + value f x ys := by
  induction xs generalizing ys with
  | nil => simp [value, plusList]
  | cons a as ih =>
    cases ys with
    | nil => simp [value, plusList]
    | cons b bs =>
      simp only [plusList, value, h, ih]
      ring

def pzero : (n : Nat) → Tower n
  | 0 => 0
  | _+1 => []

def add : (n : Nat) → Tower n → Tower n → Tower n
  | 0, a, b => a+b
  | n+1, a, b => plusList (add n) a b

theorem interp_zero (n : Nat) (v : Nat → ℝ) : interp n (pzero n) v = 0 := by
  cases n <;> simp [interp, pzero, value]

theorem interp_add (n : Nat) (a b : Tower n) (v : Nat → ℝ) :
    interp n (add n a b) v = interp n a v + interp n b v := by
  induction n generalizing v with
  | zero => simp [interp, add]
  | succ n ih => exact value_plusList (fun a => interp n a (fun k => v (k+1))) (v 0) (add n) (fun _ _ => ih _ _ _) _ _

def isZero : (n : Nat) → Tower n → Bool
  | 0, z => z == 0
  | n+1, zs => zs.all (isZero n)

theorem interp_of_isZero (n : Nat) (a : Tower n) (v : Nat → ℝ)
    (h : isZero n a = true) : interp n a v = 0 := by
  induction n generalizing v with
  | zero =>
    have ha : a = (0 : Int) := by simpa [isZero] using h
    simp [ha, interp]
  | succ n ih =>
    change value _ _ a = 0
    change a.all (isZero n) = true at h
    induction a with
    | nil => rfl
    | cons a as ht =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp [value, ih _ _ h.1, ht h.2]

def timesList {α : Type} (plus mul : α → α → α) (zero : α)
    (isZ : α → Bool) (bs : List α) : List α → List α
  | [] => []
  | a :: as =>
    let tail := zero :: timesList plus mul zero isZ bs as
    if isZ a then tail else plusList plus (bs.map (mul a)) tail

theorem value_mapped {α : Type} (f : α → ℝ) (x : ℝ) (mul : α → α → α)
    (h : ∀ a b, f (mul a b) = f a * f b) (a : α) (bs : List α) :
    value f x (bs.map (mul a)) = f a * value f x bs := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    simp only [List.map_cons, value, h, ih]
    ring

theorem value_timesList {α : Type} (f : α → ℝ) (x : ℝ)
    (plus mul : α → α → α) (z : α) (iz : α → Bool)
    (hp : ∀ a b, f (plus a b) = f a + f b)
    (hm : ∀ a b, f (mul a b) = f a * f b)
    (hz : f z = 0) (hi : ∀ a, iz a = true → f a = 0)
    (as bs : List α) :
    value f x (timesList plus mul z iz bs as) = value f x as * value f x bs := by
  induction as with
  | nil => simp [timesList, value]
  | cons a as ih =>
    rw [timesList]
    split
    · rename_i h
      simp [value, hi a h, hz, ih]
      ring
    · rw [value_plusList _ _ _ hp, value_mapped _ _ _ hm]
      simp only [value, hz, zero_add, ih]
      ring

def mul : (n : Nat) → Tower n → Tower n → Tower n
  | 0, a, b => a*b
  | n+1, a, b => timesList (add n) (mul n) (pzero n) (isZero n) b a

theorem interp_mul (n : Nat) (a b : Tower n) (v : Nat → ℝ) :
    interp n (mul n a b) v = interp n a v * interp n b v := by
  induction n generalizing v with
  | zero => simp [interp, mul]
  | succ n ih =>
    exact value_timesList (fun a => interp n a (fun k => v (k+1))) (v 0) (add n) (mul n) (pzero n) (isZero n) (fun _ _ => interp_add _ _ _ _)
      (fun _ _ => ih _ _ _) (interp_zero _ _) (fun _ h => interp_of_isZero _ _ _ h) _ _

def point (b c d e j : ℝ) : Nat → ℝ
  | 0 => b
  | 1 => c
  | 2 => d
  | 3 => e
  | _ => j

end SparseCubes.Certificate
