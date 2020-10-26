open import Data.Bool as Bool using (Bool; false; true; if_then_else_)
open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≟_; suc)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List as l using (List; filter; map; take; foldl; length)
open import Data.List.Properties
open import Data.Maybe using (to-witness)
open import Data.Fin using (fromℕ; _-_; zero)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Level using (Level)
open import Data.Vec as v using (Vec; fromList; toList; last; length; []; _∷_; [_]; _∷ʳ_; _++_; lookup; head; initLast; filter; map)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_; cong₂)
open import Data.Nat.Properties using (+-comm)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (does)
open import Data.Vec.Bounded.Base using (padRight)


record Todo : Set where
  field
    text      : String
    completed : Bool
    id        : ℕ

AddTodo : ∀ {n : ℕ} → (Vec Todo n) → String → (Vec Todo (1 + n))
AddTodo todos text =
  todos ∷ʳ
  record
    { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
    ; completed = false
    ; text      = text
    }

private
  variable
    a : Level
    A : Set a

vecLength-++ :
  ∀ {n m} (xs : Vec A n) {ys : Vec A m} →
    v.length (xs ++ ys) ≡ v.length xs + v.length ys
vecLength-++ []       = refl
vecLength-++ (x ∷ xs) = cong suc (vecLength-++ xs)

AddTodoAddsNewListItem :
  ∀ {n : ℕ} → (todos : Vec Todo n) (text : String) →
    v.length (AddTodo todos text) ≡ v.length todos + 1
AddTodoAddsNewListItem []       text = refl
AddTodoAddsNewListItem (x ∷ xs) text =
  begin
    v.length (AddTodo (x ∷ xs) text)
  ≡⟨⟩
    1 + v.length (x ∷ xs)
  ≡⟨ +-comm 1 (v.length (x ∷ xs))⟩
    v.length (x ∷ xs) + 1
  ∎

-- TODO add to std-lib
vecLast : ∀ {a} {A : Set a} {l} {n : ℕ} (xs : Vec A n) → last (xs ∷ʳ l) ≡ l
vecLast []       = refl
vecLast (_ ∷ xs) = P.trans (prop (xs ∷ʳ _)) (vecLast xs)
  where
    prop : ∀ {a} {A : Set a} {n x} (xs : Vec A (suc n)) → last (x ∷ xs) ≡ last xs
    prop xs with initLast xs
    ...        | _ , _ , refl = refl

AddTodoLastAddedElementIsTodo :
  ∀ {n} (todos : Vec Todo n) (text : String) →
    last (AddTodo todos text) ≡ 
      record
        { id        = 1
        ; completed = false
        ; text      = text
        }
AddTodoLastAddedElementIsTodo todos text = vecLast todos

-- should set (new element).completed to false
AddTodoSetsNewCompletedToFalse :
  ∀ {n} (todos : Vec Todo n) (text : String) →
    Todo.completed (last (AddTodo todos text)) ≡ false
AddTodoSetsNewCompletedToFalse todos text
  rewrite
    (AddTodoLastAddedElementIsTodo todos text) =
      refl
-- should set (new element).id to an id not existing already in the list
AddTodoSetsNewIdTo1 :
  ∀ {n} (todos : Vec Todo n) (text : String) →
    Todo.id (last (AddTodo todos text)) ≡ 1
AddTodoSetsNewIdTo1 todos text
  rewrite
    (AddTodoLastAddedElementIsTodo todos text) =
      refl
-- TODO should not touch other elements in the list

{-# COMPILE JS AddTodo =
  function (todos) {
    return function (text) {
      return [
        ...todos,
        {
          id: todos.reduce((maxId, todo) => Math.max(todo.id, maxId), -1) + 1,
          completed: false,
          text: text
        }
      ]
    }
  }
#-}

-- DeleteTodo : (List Todo) → ℕ → (List Todo)
-- DeleteTodo todos id' = filter (λ todo → Todo.id todo ≟ id') todos

private
  variable
    p : Level

DeleteTodo : ∀ {n} → (Vec Todo n) → ℕ → (Vec Todo n)
DeleteTodo todos id' =
  padRight
    record
      { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
      ; completed = false
      ; text      = ""
      }
    (v.filter (λ todo → Todo.id todo ≟ id') todos)

-- should remove element from the list unless there are no elements
-- should remove element with given id
-- should not touch other elements in the list

-- {-# COMPILE JS DeleteTodo =
--   function (todos) {
--     return function (id) {
--       return todos.filter(function (todo) {
--         return todo.id === id
--       });
--     }
--   }
-- #-}

EditTodo : ∀ {n} → (Vec Todo n) → ℕ → String → (Vec Todo n)
EditTodo todos id text =
  v.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { text = text }
    else todo)
    todos

-- should change (element with given id).text
-- should not (element with given id).id
-- should not (element with given id).completed
-- should not touch other elements in the list

-- {-# COMPILE JS EditTodo =
--   function (todos) {
--     return function (id) {
--       return function (text) {
--         return todos.map(function (todo) {
--           if (todo.id === id) {
--             todo.text = text;
--           }

--           return todo;
--         });
--       }
--     }
--   }
-- #-}

CompleteTodo : ∀ {n} → (Vec Todo n) → ℕ → (Vec Todo n)
CompleteTodo todos id =
  v.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { completed = true }
    else todo)
    todos

-- should change (element with given id).completed to true
-- should not (element with given id).id
-- should not (element with given id).text
-- should not touch other elements in the list

-- {-# COMPILE JS CompleteTodo =
--   function (todos) {
--     return function (id) {
--       return todos.map(function (todo) {
--         if (todo.id === id) {
--           todo.completed = true;
--         }

--         return todo;
--       });
--     }
--   }
-- #-}

CompleteAllTodos : ∀ {n} → (Vec Todo n) → (Vec Todo n)
CompleteAllTodos todos =
  v.map (λ todo →
    record todo { completed = true })
    todos

-- should change (all elements).completed to true
-- should not change (all elements).id
-- should not change (all elements).text

-- {-# COMPILE JS CompleteAllTodos =
--   function (todos) {
--     return todos.map(function(todo) {
--       todo.completed = true;
--       return todo;
--     });
--   }
-- #-}

ClearCompleted : ∀ {n} → (Vec Todo n) → (Vec Todo n)
ClearCompleted todos =
  padRight
    record
      { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
      ; completed = false
      ; text      = ""
      }
    (v.filter (λ todo → Bool._≟_ (Todo.completed todo) true) todos)

-- should remove all elements where completed = true
-- should not change other elements
-- should not change (all elements).text
-- should not change (all elements).id

-- {-# COMPILE JS ClearCompleted =
--   function (todos) {
--     return todos.filter(function(todo) {
--       return !todo.completed;
--     });
--   }
-- #-}

-- add-todos-length-increased-by-1 : ∀ (todos : List Todo) → length (AddTodo todos "test")
-- add-todos-length-increased-by-1 = ?
-- delete-todos-length-decreased-by-1-except-if-length-0 : ()
-- edit-todos-length-not-changed : ()
-- complete-todos-length-not-changed : ()
-- complete-all-todos-length-not-changed : ()

-- clear-completed-todos-not-have-completed : ()

-- should not generate duplicate ids after CLEAR_COMPLETE

-- data Action : Set where
--   ADD_TODO DELETE_TODO EDIT_TODO COMPLETE_TODO COMPLETE_ALL_TODOS CLEAR_COMPLETED : Action

-- Reducer : Todos → Action → Todos
-- Reducer todos ADD_TODO = AddTodo todos id
-- Reducer todos DELETE_TODO = DeleteTodo todos id
-- Reducer todos EDIT_TODO = EditTodo todos id
-- Reducer todos COMPLETE_TODO = CompleteTodo todos id
-- Reducer todos COMPLETE_ALL_TODOS = CompleteAllTodos todos id
-- Reducer todos CLEAR_COMPLETED = ClearCompleted todos id
