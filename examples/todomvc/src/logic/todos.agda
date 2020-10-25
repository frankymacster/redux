open import Data.Bool as Bool using (Bool; false; true; if_then_else_)
open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≟_; suc)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List; filter; map; take; foldl; length)
open import Data.List.Properties
open import Data.Maybe using (to-witness)
open import Data.Fin using (fromℕ; _-_; zero)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Vec using (Vec; fromList; toList; last; []; _∷_; [_]; _∷ʳ_; _++_; lookup; head; initLast)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_; cong₂)

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

AddTodoAddsNewListItem :
  ∀ {n : ℕ} → (todos : Vec Todo n) (text : String) →
    length (toList (AddTodo todos text)) ≡ length (toList todos) + 1
AddTodoAddsNewListItem todos text = fromList (length-++ (toList todos))

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
-- should not touch other elements in the list

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

DeleteTodo : (List Todo) → ℕ → (List Todo)
DeleteTodo todos id' = filter (λ todo → Todo.id todo ≟ id') todos

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

EditTodo : (List Todo) → ℕ → String → (List Todo)
EditTodo todos id text =
  map (λ todo →
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

CompleteTodo : (List Todo) → ℕ → (List Todo)
CompleteTodo todos id =
  map (λ todo →
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

CompleteAllTodos : (List Todo) → (List Todo)
CompleteAllTodos todos =
  map (λ todo →
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

ClearCompleted : (List Todo) → (List Todo)
ClearCompleted todos =
  filter (λ todo → Bool._≟_ (Todo.completed todo) true) todos

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
