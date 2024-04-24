{-# OPTIONS --guardedness #-}
open import IO
open import Relation.Binary.PropositionalEquality.Core
open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Product
open import Agda.Primitive renaming (Set to Type)
open import Data.Nat
open import Data.Nat.Show

record Stack {l : Level} (T : Type l) : Type (lsuc l) where
  field
    S : Type l
    empty : S
    push : T → S → S
    pop : S → Maybe (T × S)

-- open Stack

record LawfulStack {l : Level} {T : Type l} (S : Stack T) : Type l where
  open Stack S
  field
    pop-push : ∀ {t s} → pop (push t s) ≡ just (t , s)

ListStack : ∀ {l} (T : Type l) → Stack T
ListStack T = λ where
  .S → List T
  .empty → []
  .push t s → t ∷ s
  .pop [] → nothing
  .pop (x ∷ s) → just (x , s)
    where open Stack

instance
  LawfulListStack : ∀ {l} {T : Type l} → LawfulStack (ListStack T)
  LawfulListStack = λ where
    .pop-push → refl
      where open LawfulStack

do-stuff : (S : Stack ℕ) → {{l : LawfulStack S}} → ℕ
do-stuff S {{l}} = let
  a = empty
  b = push 1 a
  c = push 5 b
  in
    proj₁
      (to-witness-T
        (pop c)
        (subst (λ m → T (is-just m)) (sym pop-push) _))
  where
    open Stack S
    open LawfulStack l

main : Main
main = run
  ( (putStrLn (show (do-stuff (ListStack ℕ))) >>
    -- I would use another Stack implementation, if I had one
    (putStrLn (show (do-stuff (ListStack ℕ))))))
