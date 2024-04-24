import Std.Data.Array.Basic
import Std.Data.Array.Lemmas

structure Stack (T : Type u) where
  S : Type v
  empty : S
  push : T → S → S
  pop : S → Option (T × S)

class LawfulStack {T : Type u} (S : Stack T) where
  pop_push : ∀ {t s}, S.pop (S.push t s) = some (t, s)

def ListStack (T : Type u) : Stack T where
  S := List T
  empty := []
  push t s := t :: s
  pop
  | [] => none
  | x :: xs => some (x, xs)

instance (T : Type u) : LawfulStack (ListStack T) where
  pop_push {t s} := by rfl

def ArrayStack (T : Type u) [Inhabited T] : Stack T where
  S := Array T
  empty := Array.mkEmpty 8
  push t s := s.push t
  pop s := match s.size with
  | 0 => none
  | n + 1 =>
    let last := s.get! n
    let heads := s.pop
    some (last, heads)

instance (T : Type u) [Inhabited T] : LawfulStack (ArrayStack T) where
  pop_push := by
    intros t s
    dsimp [ArrayStack]
    rw [Array.size_push]; simp
    rw [Array.get?_push_eq]; simp

def do_thing (S : Stack Nat) [ℓ : LawfulStack S] : Nat :=
  let a := S.empty
  let b := S.push 1 a
  let c := S.push 5 b
  ((S.pop c).get
    (by rw [LawfulStack.pop_push]; simp)).fst

#eval do_thing (ListStack Nat)
#eval do_thing (ArrayStack Nat)

#check Nat.rec

def main : IO Unit := do
  IO.println (do_thing (ListStack Nat))
  IO.println (do_thing (ArrayStack Nat))
