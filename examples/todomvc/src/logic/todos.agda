open import Data.Bool as Bool using (Bool; false; true; if_then_else_; not)
open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≟_; suc; _>_; _<_; _∸_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List as l using (List; filter; map; take; foldl; length; []; _∷_)
open import Data.List.Properties
-- open import Data.List.Extrema using (max)
open import Data.Maybe using (to-witness)
open import Data.Fin using (fromℕ; _-_; zero; Fin)
open import Data.Fin.Properties using (≤-totalOrder)
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
open import Function using (_∘_)
open import Data.List.Extrema ℕₚ.≤-totalOrder

-- TODO add to std-lib
open import Relation.Nullary

dec-¬ : ∀ {a} {P : Set a} → Dec P → Dec (¬ P)
dec-¬ (yes p) = no λ prf → prf p
dec-¬ (no ¬p) = yes ¬p

vecLast : ∀ {a} {A : Set a} {l} {n : ℕ} (xs : Vec A n) → last (xs ∷ʳ l) ≡ l
vecLast []       = refl
vecLast (_ ∷ xs) = P.trans (prop (xs ∷ʳ _)) (vecLast xs)
  where
    prop : ∀ {a} {A : Set a} {n x} (xs : Vec A (suc n)) → last (x v.∷ xs) ≡ last xs
    prop xs with initLast xs
    ...        | _ , _ , refl = refl

allButLast : ∀ {a} {A : Set a} → List A → List A
allButLast [] = l.[]
allButLast (x l.∷ l.[]) = (x l.∷ l.[])
allButLast (x l.∷ xs) = x l.∷ allButLast xs


record Todo : Set where
  field
    text      : String
    completed : Bool
    id        : ℕ

TodoListLast : List Todo → Todo
TodoListLast []             = record {}
TodoListLast todos@(x ∷ xs) = v.last (v.fromList todos)


AddTodo : List Todo → String → List Todo
AddTodo todos text =
  todos l.∷ʳ
  record
    { id        = (max 0 (l.map (λ e → Todo.id e) todos)) + 1
    ; completed = false
    ; text      = text
    }

AddTodoAddsNewListItem :
  (todos : List Todo) (text : String) →
    l.length (AddTodo todos text) ≡ l.length todos + 1
AddTodoAddsNewListItem todos text = length-++ todos

AddTodoSetsNewCompletedToFalse :
  (todos : List Todo) (text : String) →
    Todo.completed (TodoListLast (AddTodo todos text)) ≡ false
AddTodoSetsNewCompletedToFalse todos text = {!   !}

AddTodoSetsNewIdToNonExistingId :
  (todos : List Todo) (text : String) →
    l.length (l.filter (λ todo → dec-¬ (Todo.id todo ≟ Todo.id (TodoListLast (AddTodo todos text)))) (AddTodo todos text)) ≡ 1
AddTodoSetsNewIdToNonExistingId todos text = {!   !}

AddTodoSetsNewTextToText :
  (todos : List Todo) (text : String) →
    Todo.text (TodoListLast (AddTodo todos text)) ≡ text
AddTodoSetsNewTextToText todos text = {!   !}

AddTodoDoesntChangeIds :
  (todos : List Todo) (text : String) →
    l.map  (λ todo → Todo.id todo) (allButLast (AddTodo todos text)) ≡ l.map (λ todo → Todo.id todo) todos
AddTodoDoesntChangeIds todos text = {!   !}

AddTodoDoesntChangeText :
  (todos : List Todo) (text : String) →
    l.map (λ todo → Todo.text todo) (allButLast (AddTodo todos text)) ≡ l.map (λ todo → Todo.text todo) todos
AddTodoDoesntChangeText todos text = {!   !}

AddTodoDoesntChangeCompleted :
  (todos : List Todo) (text : String) →
    l.map (λ todo → Todo.completed todo) (allButLast (AddTodo todos text)) ≡ l.map (λ todo → Todo.completed todo) todos
AddTodoDoesntChangeCompleted todos text = {!   !}

AddTodo-not-comm :
  (todos : List Todo) →
    (text1 : String) →
      (text2 : String) →
  ¬ (AddTodo (AddTodo todos text1) text2 ≡ AddTodo (AddTodo todos text2) text1)
AddTodo-not-comm todos text1 text2 = {!   !}

-- {-# COMPILE JS AddTodo =
--   function (todos) {
--     return function (text) {
--       return [
--         ...todos,
--         {
--           id: todos.reduce((maxId, todo) => Math.max(todo.id, maxId), -1) + 1,
--           completed: false,
--           text: text
--         }
--       ]
--     }
--   }
-- #-}


DeleteTodo :
  ∀ {n} →
    (List Todo)
      → ℕ →
        (List Todo)
DeleteTodo todos id' =
  l.filter (λ todo → dec-¬ (Todo.id todo ≟ id')) todos

DeleteTodoRemoveTodoWithId :
  (todos : List Todo) →
    (id' : ℕ) →
      l.length (l.filter (λ todo → Todo.id todo ≟ id') (DeleteTodo todos id')) ≡ 0
DeleteTodoRemoveTodoWithId todos id' = {!   !}

DeleteTodoRemoves1Element :
  (todos : List Todo) →
    (id' : ℕ) →
      l.length (DeleteTodo todos id') ≡ l.length todos ∸ 1
DeleteTodoRemoves1Element = {!   !}

DeleteTodoDoesntChangeIds :
  (todos : List Todo) (id : ℕ) →
    l.map  (λ todo → Todo.id todo) (DeleteTodo todos id) ≡ l.map (λ todo → Todo.id todo) (l.filter (λ todo → dec-¬ (Todo.id todo ≟ id)) todos)
DeleteTodoDoesntChangeIds todos id = {!   !}

DeleteTodoDoesntChangeText :
  (todos : List Todo) (id : ℕ) →
    l.map (λ todo → Todo.id todo) (DeleteTodo todos id) ≡ l.map (λ todo → Todo.id todo) (l.filter (λ todo → dec-¬ (Todo.id todo ≟ id)) todos)
DeleteTodoDoesntChangeText todos id = {!   !}

DeleteTodoDoesntChangeCompleted :
  (todos : List Todo) (id : ℕ) →
    l.map (λ todo → Todo.completed todo) (DeleteTodo todos id) ≡ l.map (λ todo → Todo.completed todo) (l.filter (λ todo → dec-¬ (Todo.id todo ≟ id)) todos)
DeleteTodoDoesntChangeCompleted todos id = {!   !}

DeleteTodo-idem :
  (todos : List Todo) →
    (id' : ℕ) →
      DeleteTodo (DeleteTodo todos id') id' ≡ DeleteTodo todos id'
DeleteTodo-idem todos id' =
  filter-idem (λ e → dec-¬ (Todo.id e ≟ id')) todos

-- {-# COMPILE JS DeleteTodo =
--   function (todos) {
--     return function (id) {
--       return todos.filter(function (todo) {
--         return todo.id !== id
--       });
--     }
--   }
-- #-}


-- EditTodo: can't use updateAt since id doesn't necessarily correspond to Vec index
EditTodo : (List Todo) → ℕ → String → (List Todo)
EditTodo todos id text =
  l.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { text = text }
    else todo)
    todos

EditTodoChangesText :
  (todos : List Todo) (id : ℕ) (text : String) →
    l.map (λ todo → Todo.text todo) (l.filter (λ todo → Todo.id todo ≟ id) (EditTodo todos id text)) ≡ text l.∷ l.[]
EditTodoChangesText todos id text = {!   !}

EditTodoDoesntChangeIds :
  (todos : List Todo) (id : ℕ) (text : String) →
    l.map (λ todo → Todo.id todo) (EditTodo todos id text) ≡ l.map (λ todo → Todo.id todo) todos
EditTodoDoesntChangeIds todos id text = {!   !}

EditTodoDoesntChangeOthersText :
  (todos : List Todo) (id : ℕ) (text : String) →
    l.map (λ todo → Todo.text todo) (EditTodo todos id text) ≡ l.map (λ todo → Todo.text todo) (l.filter (λ todo → dec-¬ (Todo.id todo ≟ id)) todos)
EditTodoDoesntChangeOthersText todos id text = {!   !}

EditTodoDoesntChangeCompleted :
  (todos : List Todo) (id : ℕ) (text : String) →
    l.map (λ todo → Todo.completed todo) (EditTodo todos id text) ≡ l.map (λ todo → Todo.completed todo) todos
EditTodoDoesntChangeCompleted todos id text = {!   !}

EditTodoLengthUnchanged :
  (todos : List Todo) →
    (id' : ℕ) →
      (text : String) →
        l.length (EditTodo todos id' text) ≡ l.length todos
EditTodoLengthUnchanged todos id' text = {!   !}

EditTodo-idem :
  (todos : List Todo) →
    (id' : ℕ) →
      (text : String) →
        EditTodo (EditTodo todos id' text) id' text ≡ EditTodo todos id' text
EditTodo-idem todos id' text =
  begin
    EditTodo (EditTodo todos id' text) id' text
  ≡⟨ {!   !} ⟩
    EditTodo todos id' text
  ∎

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
  l.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { completed = true }
    else todo)
    todos

CompleteTodoChangesCompleted :
  (todos : List Todo) (id : ℕ) →
    l.map (λ todo → Todo.completed todo) (l.filter (λ todo → Todo.id todo ≟ id) (CompleteTodo todos id)) ≡ true l.∷ l.[] 
CompleteTodoChangesCompleted todos id = {!   !}

CompleteTodoDoesntChangeIds :
  (todos : List Todo) (id : ℕ) →
    l.map (λ todo → Todo.id todo) (CompleteTodo todos id) ≡ l.map (λ todo → Todo.id todo) todos
CompleteTodoDoesntChangeIds todos id = {!   !}

CompleteTodoDoesntChangeText :
  (todos : List Todo) (id : ℕ) →
    l.map (λ todo → Todo.text todo) (CompleteTodo todos id) ≡ l.map (λ todo → Todo.text todo) todos
CompleteTodoDoesntChangeText todos id = {!   !}

CompleteTodoDoesntChangeOthersCompleted :
  (todos : List Todo) (id : ℕ) →
    l.map (λ todo → Todo.completed todo) (CompleteTodo todos id) ≡ l.map (λ todo → Todo.completed todo) (l.filter (λ todo → dec-¬ (Todo.id todo ≟ id)) todos)
CompleteTodoDoesntChangeOthersCompleted todos id = {!   !}

CompleteTodoLengthUnchanged :
  (todos : List Todo) →
    (id' : ℕ) →
      l.length (CompleteTodo todos id') ≡ l.length todos
CompleteTodoLengthUnchanged todos id' = {!   !}

CompleteTodo-idem :
  (todos : List Todo) →
    (id' : ℕ) →
      CompleteTodo (CompleteTodo todos id') id' ≡ CompleteTodo todos id'
CompleteTodo-idem todos id' =
  begin
    CompleteTodo (CompleteTodo todos id') id'
  ≡⟨ {!   !} ⟩
    CompleteTodo todos id'
  ∎

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


CompleteAllTodos : List Todo → List Todo
CompleteAllTodos todos =
  l.map (λ todo →
    record todo { completed = true })
    todos

CompleteAllTodosAllCompleted :
  (todos : List Todo) →
    l.length (l.filter (λ todo → (Todo.completed todo) Bool.≟ false) (CompleteAllTodos todos)) ≡ 0
CompleteAllTodosAllCompleted todos = {!   !}

CompleteAllTodosDoesntChangeIds :
  (todos : List Todo) →
    l.map (λ todo → Todo.id todo) (CompleteAllTodos todos) ≡ l.map (λ todo → Todo.id todo) todos
CompleteAllTodosDoesntChangeIds todos = {!   !}

CompleteAllTodosDoesntChangeText :
  (todos : List Todo) →
    l.map (λ todo → Todo.text todo) (CompleteAllTodos todos) ≡ l.map (λ todo → Todo.text todo) todos
CompleteAllTodosDoesntChangeText todos = {!   !}

CompleteAllTodosLengthUnchanged :
  (todos : List Todo) →
    l.length (CompleteAllTodos todos) ≡ l.length todos
CompleteAllTodosLengthUnchanged todos = {!   !}

CompleteAllTodos-idem :
  (todos : List Todo) →
    CompleteAllTodos (CompleteAllTodos todos) ≡ CompleteAllTodos todos
CompleteAllTodos-idem todos = {!   !}

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
  (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)

ClearCompletedRemovesOnlyCompleted :
  (todos : List Todo) →
    l.map (λ todo → Todo.completed todo) (ClearCompleted todos) ≡ l.map (λ todo → Todo.completed todo) (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedRemovesOnlyCompleted todos = {!   !}

ClearCompletedDoesntChangeCompleted :
  (todos : List Todo) →
    l.map (λ todo → Todo.completed todo) (ClearCompleted todos) ≡ l.map (λ todo → Todo.completed todo) (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedDoesntChangeCompleted todos = {!   !}

ClearCompletedDoesntChangeIds :
  (todos : List Todo) →
    l.map (λ todo → Todo.id todo) (ClearCompleted todos) ≡ l.map (λ todo → Todo.id todo) (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedDoesntChangeIds todos = {!   !}

ClearCompletedDoesntChangeText :
  (todos : List Todo) →
    l.map (λ todo → Todo.text todo) (ClearCompleted todos) ≡ l.map (λ todo → Todo.text todo) (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedDoesntChangeText todos = {!   !}

ClearCompleted-idem :
  (todos : List Todo) →
      ClearCompleted (ClearCompleted todos) ≡ ClearCompleted todos
ClearCompleted-idem todos =
  filter-idem (λ e → dec-¬ (Todo.completed e Bool.≟ true)) todos

-- {-# COMPILE JS ClearCompleted =
--   function (todos) {
--     return todos.filter(function(todo) {
--       return !todo.completed;
--     });
--   }
-- #-}
