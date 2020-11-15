open import Data.Bool as Bool using (Bool; false; true; if_then_else_; not)
open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≟_; suc; _>_; _<_; _∸_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List as l using (List; filter; map; take; foldl; length)
open import Data.List.Properties
open import Data.Maybe using (to-witness)
open import Data.Fin using (fromℕ; _-_; zero)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_; Σ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Level using (Level)
open import Data.Vec as v using (Vec; fromList; toList; last; length; []; _∷_; [_]; _∷ʳ_; _++_; lookup; head; initLast; filter; map)
open import Data.Vec.Bounded as vb using ([]; _∷_; fromVec; filter; Vec≤)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_; cong₂)
open import Data.Nat.Properties using (+-comm)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (does)
open import Data.Vec.Bounded.Base using (padRight; ≤-cast)
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary.Decidable.Core using (dec-false)

-- essentially a List String

record Todo : Set where
  field
    text      : String

AddTodo :
  ∀ {n : ℕ} →
    (Vec Todo n) →
      String →
        (Vec Todo (1 + n))
AddTodo todos text =
  todos ∷ʳ
  record
    { text = text
    }

AddTodoAddsNewListItem :
  ∀ {n : ℕ} →
    (todos : Vec Todo n) (text : String) →
      v.length (AddTodo todos text) ≡ v.length todos + 1
AddTodoAddsNewListItem []    text = refl
AddTodoAddsNewListItem todos text = +-comm 1 (v.length todos)

AddTodoLastAddedElementIsTodo :
  ∀ {n} (todos : Vec Todo n) (text : String) →
    last (AddTodo todos text) ≡ 
      record
        { text = text
        }
AddTodoLastAddedElementIsTodo todos text = vecLast todos
  where
    vecLast : ∀ {a} {A : Set a} {l} {n : ℕ} (xs : Vec A n) → last (xs ∷ʳ l) ≡ l
    vecLast []       = refl
    vecLast (_ ∷ xs) = P.trans (prop (xs ∷ʳ _)) (vecLast xs)
      where
        prop : ∀ {a} {A : Set a} {n x} (xs : Vec A (suc n)) → last (x v.∷ xs) ≡ last xs
        prop xs with initLast xs
        ...        | _ , _ , refl = refl

AddTodoAddedTodoHasGivenText :
  ∀ {n} (todos : Vec Todo n) (text : String) →
    Todo.text (last (AddTodo todos text)) ≡ text
AddTodoAddedTodoHasGivenText todos text
  rewrite
    (AddTodoLastAddedElementIsTodo todos text) =
      refl