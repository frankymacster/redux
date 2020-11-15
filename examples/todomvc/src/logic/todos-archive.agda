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
vecLast : ∀ {a} {A : Set a} {l} {n : ℕ} (xs : Vec A n) → last (xs ∷ʳ l) ≡ l
vecLast []       = refl
vecLast (_ ∷ xs) = P.trans (prop (xs ∷ʳ _)) (vecLast xs)
  where
    prop : ∀ {a} {A : Set a} {n x} (xs : Vec A (suc n)) → last (x v.∷ xs) ≡ last xs
    prop xs with initLast xs
    ...        | _ , _ , refl = refl



-- operations
  -- AddTodo
  -- DeleteTodo
  -- CompleteTodo
  -- ClearCompleted
  -- CompleteAllTodos

-- horizontal properties
  -- AddTodo
  --   non-commutative
  -- DeleteTodo
  --   idempotent
  -- CompleteTodo
  --   idempotent
  -- ClearCompleted
  --   idempotent
  -- CompleteAllTodos
  --   idempotent
  -- EditTodo
  --   EditTodo - EditTodo Todo list length doesn't change

-- vertical properties
  -- AddTodo
  --   AddTodoSetsNewCompletedToFalse
  --   AddTodoSetsNewIdToNonExistingId
  --   AddTodoSetsNewTextToText
  --   doesn't change id of other Todos
  --   doesn't change text of other Todos
  --   doesn't change completed of other Todos
  -- DeleteTodo
  --   DeleteTodoRemoveTodoWithId
  --   DeleteTodoRemoves1Element
  --     only way to add todo is with AddTodo and AddTodo gives non existing id to new todo
  --   doesn't change id of other Todos
  --   doesn't change text of other Todos
  --   doesn't change completed of other Todos
  -- CompleteTodo
  --   CompleteTodoSetsTodoWithIdCompletedToTrue
  --   doesn't touch any other Todo
  --   doesn't change id of any Todo
  --   doesn't change text of any Todo
  -- ClearCompleted
  --   doesn't remove Todos where completed = false
  --   doesn't change id of any Todo
  --   doesn't change completed of any Todo
  --   doesn't change text of any Todo
  -- CompleteAllTodos
  --   all Todos have completed = true
  --   doesn't change id of any Todo
  --   doesn't change text of any Todo
  -- EditTodo
  --   modifies Todo with given id's text
  --   doesn't change the id
  --   doesn't change completed
  --   doesn't modify other Todos

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

ListAddTodo : List Todo → String → List Todo
ListAddTodo todos text =
  todos l.∷ʳ
  record
    { id        = (max 0 (l.map (λ e → Todo.id e) todos)) + 1
    ; completed = false
    ; text      = text
    }

ListAddTodoAddsNewListItem :
  (todos : List Todo) (text : String) →
    l.length (ListAddTodo todos text) ≡ l.length todos + 1
ListAddTodoAddsNewListItem todos text = length-++ todos


listVec : Vec ℕ 1
listVec = v.fromList (2 l.∷ l.[])

listLast : ℕ
listLast = v.last (v.fromList (2 l.∷ l.[]))

listLastIs2 : v.last (v.fromList (2 l.∷ l.[])) ≡ 2 
listLastIs2 = refl

record Id : Set where
  field
    id : ℕ


natListToVec : (xs : List ℕ) → Vec ℕ (l.length xs)
natListToVec nats = v.fromList nats

-- natListLast : List ℕ → ℕ
-- natListLast nats = v.last {(l.length nats) ∸ 1} (v.fromList nats)

natListLast : List ℕ → ℕ
natListLast []            = 0
natListLast nats@(x ∷ xs) = v.last (v.fromList nats)

natListFromList : v.fromList (1 l.∷ l.[]) ≡ (1 v.∷ v.[])
natListFromList = refl

ListOf1sConcatFromList : v.fromList (1 l.∷ l.[] l.++ 1 l.∷ l.[]) ≡ (1 v.∷ v.[] v.++ 1 v.∷ v.[])
ListOf1sConcatFromList = refl

open import Data.Nat.Properties

{-# BUILTIN SIZE     Size   #-}
private
  variable
    a : Level
    A : Set a
    i : Size


vec-length-++ :
  ∀ {n : ℕ} (xs : Vec A n) {ys} →
    v.length (xs v.++ ys) ≡ v.length xs + v.length ys
vec-length-++ xs {ys} = refl

-- vec-fromList-++ :
--   (as bs : List A) →
--     v.fromList (as l.++ bs) ≡ v.fromList as v.++ v.fromList bs
-- vec-fromList-++ []       bs = v.[]
-- vec-fromList-++ (a ∷ as) bs = ?


-- natListConcatFromList : (nats1 : List ℕ) → (nats2 : List ℕ) → v.fromList (nats1 l.++ nats2) ≡ (nats1 v.++ nats2)
-- natListConcatFromList nats = ?


-- natListConcatFromList : (nats : List ℕ) → v.fromList (nats l.++ (1 l.∷ l.[])) ≡ ((v.fromList nats) v.++ (1 v.∷ v.[]))
-- natListConcatFromList = {!   !}

natListConcatLast : (nats : List ℕ) → natListLast (nats l.++ 1 l.∷ l.[]) ≡ 1
natListConcatLast [] = refl
natListConcatLast nats@(x ∷ xs) =
  begin
    natListLast (nats l.++ 1 l.∷ l.[])
  ≡⟨⟩
    v.last (v.fromList ((x l.∷ xs) l.++ 1 l.∷ l.[]))
  ≡⟨⟩
    v.last (v.fromList ((x l.∷ xs) l.++ 1 l.∷ l.[]))
  ≡⟨ {!   !} ⟩
    1
  ∎

TodoListLast : List Todo → Todo
TodoListLast []             = record {}
TodoListLast todos@(x ∷ xs) = v.last (v.fromList todos)


ListWith2ToVec : v.fromList (2 l.∷ l.[]) ≡ 2 v.∷ v.[]
ListWith2ToVec = refl

idListLastIdIs2 : Id.id (v.last (v.fromList (record {id = 2} l.∷ l.[]))) ≡ 2
idListLastIdIs2 = refl

todoListLastIdIs2 : Todo.id (v.last (v.fromList (record {id = 2; text = ""; completed = false} l.∷ l.[]))) ≡ 2
todoListLastIdIs2 = refl

ListTodoLastTextIsText :
  (todos : List Todo) (text : String) →
    Todo.text (v.last (v.fromList (
      record
      { text = text
      ; completed = false
      ; id = max 0 (l.map Todo.id todos) + 1
      } l.∷ l.[]
    ))) ≡ text
ListTodoLastTextIsText todos text = refl

-- ListAddTodoLastAddedElementIsTodo :
--   (todos : List Todo) (text : String) →
--     Todo.text (TodoListLast (ListAddTodo todos text)) ≡ text
-- ListAddTodoLastAddedElementIsTodo []       text = refl
-- ListAddTodoLastAddedElementIsTodo todos@(x ∷ xs) text =
--   begin
--     Todo.text (TodoListLast (ListAddTodo todos text))
--   ≡⟨⟩
--     Todo.text (
--       TodoListLast (
--         todos
--         l.++
--         (
--           record
--           { text = text
--           ; completed = false
--           ; id = max 0 (l.map Todo.id todos) + 1
--           }
--           l.∷
--           l.[]
--         )
--       )
--     )
--   ≡⟨⟩
--     Todo.text (
--       record
--       { text = text
--       ; completed = false
--       ; id = max 0 (l.map Todo.id todos) + 1
--       }
--     )
--   ≡⟨ ? ⟩
--     text
--   ∎


-- open import Data.Nat.Base

-- infixr 5 _vb∷ʳ_
-- _vb∷ʳ_ : ∀ {n} → Vec≤ A n → A → Vec≤ A (suc n)
-- (as , p) vb∷ʳ a = as , s≤s p v.∷ʳ a

-- Vec≤AddTodo : ∀ {n : ℕ} → (Vec≤ Todo n) → String → (Vec≤ Todo (1 + n))
-- Vec≤AddTodo todos text =
--   todos vb∷ʳ
--   record
--     { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
--     ; completed = false
--     ; text      = text
--     }

vecLength-++ :
  ∀ {n m} (xs : Vec A n) {ys : Vec A m} →
    v.length (xs ++ ys) ≡ v.length xs + v.length ys
vecLength-++ []       = refl
vecLength-++ (x ∷ xs) = cong suc (vecLength-++ xs)

AddTodoAddsNewListItem :
  ∀ {n : ℕ} → (todos : Vec Todo n) (text : String) →
    v.length (AddTodo todos text) ≡ v.length todos + 1
AddTodoAddsNewListItem []       text = refl
AddTodoAddsNewListItem (x v.∷ xs) text =
  begin
    v.length (AddTodo (x v.∷ xs) text)
  ≡⟨⟩
    1 + v.length (x v.∷ xs)
  ≡⟨ +-comm 1 (v.length (x v.∷ xs))⟩
    v.length (x v.∷ xs) + 1
  ∎

ListTodoAddTodoAddsNewListItem :
  (todos : List Todo) (text : String) →
    l.length (ListAddTodo todos text) ≡ l.length todos + 1
ListTodoAddTodoAddsNewListItem []       text = refl
ListTodoAddTodoAddsNewListItem todos text =
  +-comm 1 (l.length todos)

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

open import Relation.Nullary

dec-¬ : ∀ {a} {P : Set a} → Dec P → Dec (¬ P)
dec-¬ (yes p) = no λ prf → prf p
dec-¬ (no ¬p) = yes ¬p

VecFilter : Vec≤.vec (v.filter (λ e → e ≟ 2) (2 v.∷ 1 v.∷ v.[])) ≡ (2 v.∷ v.[])
VecFilter = refl

-- VecFilter' : Vec≤.vec (v.filter (λ e → dec-¬ (e ≟ 2)) (2 v.∷ 1 v.∷ v.[])) ≡ (1 v.∷ v.[])
-- VecFilter' = refl

-- VecFilter'' : {n : ℕ} → Vec≤.vec (v.filter (λ e → e ≟ 2) (n v.∷ v.[])) ≡ 2 v.∷ v.[]
-- VecFilter'' = ?

-- VecFilter''' : {n : ℕ} → v.filter (λ e → e ≟ n) (n v.∷ v.[]) ≡ n vb.∷ vb.[]
-- VecFilter''' = {!   !}


-- ListFilter : l.filter (λ e → e ≟ 2) (2 l.∷ l.[]) ≡ 2 l.∷ l.[]
-- ListFilter = refl

-- ListFilter' : {n : ℕ} → l.filter (λ e → e ≟ n) (n l.∷ l.[]) ≡ n l.∷ l.[]
-- ListFilter' = {!   !}

-- DeleteNat : ∀ {n m} → (Vec ℕ n) → ℕ → (Vec ℕ m)
-- DeleteNat nats nat = Vec≤.vec (v.filter (λ e → e ≟ nat) nats)

DeleteNat : List ℕ → ℕ → List ℕ
DeleteNat nats nat = l.filter (λ e → dec-¬ (e ≟ nat)) nats

DeleteNat-idem :
  (nats : List ℕ) →
    (nat : ℕ) →
      DeleteNat (DeleteNat nats nat) nat ≡ DeleteNat nats nat
DeleteNat-idem nats nat = filter-idem (λ e → dec-¬ (e ≟ nat)) nats
  -- begin
  --   DeleteNat (DeleteNat nats nat) nat
  -- ≡⟨⟩
  --   DeleteNat (l.filter (λ e → dec-¬ (e ≟ nat)) nats) nat
  -- ≡⟨⟩
  --   l.filter (λ e → dec-¬ (e ≟ nat)) (l.filter (λ e → dec-¬ (e ≟ nat)) nats)
  -- ≡⟨⟩
  --   (l.filter (λ e → dec-¬ (e ≟ nat)) ∘ l.filter (λ e → dec-¬ (e ≟ nat))) nats
  -- ≡⟨ filter-idem (λ e → dec-¬ (e ≟ nat)) nats ⟩
  --   l.filter (λ e → dec-¬ (e ≟ nat)) nats
  -- ≡⟨⟩
  --   DeleteNat nats nat
  -- ∎

private
  variable
    p : Level

-- VecTodoDeleteTodo :
--   ∀ {n} →
--     (Vec Todo n)
--       → ℕ →
--         (Vec Todo n)
-- VecTodoDeleteTodo todos id' =
--   Vec≤.vec (v.filter (λ todo → dec-¬ (Todo.id todo ≟ id')) todos)

ListTodoDeleteTodo :
  ∀ {n} →
    (List Todo)
      → ℕ →
        (List Todo)
ListTodoDeleteTodo todos id' =
  l.filter (λ todo → dec-¬ (Todo.id todo ≟ id')) todos

ListTodoDeleteTodo-idem :
  (todos : List Todo) →
    (id' : ℕ) →
      ListTodoDeleteTodo (ListTodoDeleteTodo todos id') id' ≡ ListTodoDeleteTodo todos id'
ListTodoDeleteTodo-idem todos id' =
  filter-idem (λ e → dec-¬ (Todo.id e ≟ id')) todos

-- Vec≤DeleteTodo : ∀ {n} → (Vec≤ Todo n) → ℕ → (Vec≤ Todo n)
-- Vec≤DeleteTodo todos id' = vb.filter (λ todo → Todo.id todo ≟ id') todos




-- filterProof : v.filter (λ e → e ≟ 2) (2 v.∷ v.[]) ≡ (2 vb.∷ vb.[])
-- filterProof = refl

-- filterProof' : v.filter (λ e → dec-¬ (e ≟ 2)) (2 v.∷ v.[]) ≡ vb.[]
-- filterProof' = refl

-- dropWhileProof : v.dropWhile (λ e → e ≟ 2) (2 v.∷ 3 v.∷ v.[]) ≡ 3 vb.∷ vb.[]
-- dropWhileProof = refl

-- dropWhileProof' : v.dropWhile (λ e → e ≟ 3) (2 v.∷ 3 v.∷ v.[]) ≡ (2 vb.∷ 3 vb.∷ vb.[])
-- dropWhileProof' = refl

-- todoFilterProof :
--   v.filter
--     (λ todo → dec-¬ ((Todo.id todo) ≟ 2))
--     (
--       record
--         { id        = 2
--         ; completed = false
--         ; text      = ""
--         }
--       v.∷
--       record
--         { id        = 1
--         ; completed = false
--         ; text      = ""
--         }
--       v.∷
--       v.[]
--     )
--   ≡
--   (
--     record
--       { id        = 1
--       ; completed = false
--       ; text      = ""
--       }
--     vb.∷
--     vb.[]
--   )
-- todoFilterProof = refl
      

-- should remove element from the list unless there are no elements
-- should remove element with given id
-- DeleteTodoRemoveTodoById :
--   ∀ {n : ℕ} (id' : ℕ) (todos : Vec Todo n) →
--     padRight
--       record
--         { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
--         ; completed = false
--         ; text      = ""
--         }
--       (v.filter (λ todo → dec-¬ ((Todo.id todo) ≟ id')) (DeleteTodo todos id'))
--     ≡ DeleteTodo todos id'
-- DeleteTodoRemoveTodoById id' v.[] = refl
-- DeleteTodoRemoveTodoById id' (x v.∷ xs) = {!   !} (DeleteTodoRemoveTodoById xs)

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
VecTodoEditTodo : ∀ {n} → (Vec Todo n) → ℕ → String → (Vec Todo n)
VecTodoEditTodo todos id text =
  v.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { text = text }
    else todo)
    todos

ListTodoEditTodo : (List Todo) → ℕ → String → (List Todo)
ListTodoEditTodo todos id text =
  l.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { text = text }
    else todo)
    todos

ListTodoEditTodo-idem :
  (todos : List Todo) →
    (id' : ℕ) →
      (text : String) →
        ListTodoEditTodo (ListTodoEditTodo todos id' text) id' text ≡ ListTodoEditTodo todos id' text
ListTodoEditTodo-idem todos id' text =
  begin
    ListTodoEditTodo (ListTodoEditTodo todos id' text) id' text
  ≡⟨ {!   !} ⟩
    ListTodoEditTodo todos id' text
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

VecTodoCompleteTodo : ∀ {n} → (Vec Todo n) → ℕ → (Vec Todo n)
VecTodoCompleteTodo todos id =
  v.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { completed = true }
    else todo)
    todos

ListTodoCompleteTodo : (List Todo) → ℕ → (List Todo)
ListTodoCompleteTodo todos id =
  l.map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { completed = true }
    else todo)
    todos

ListTodoCompleteTodo-idem :
  (todos : List Todo) →
    (id' : ℕ) →
      ListTodoCompleteTodo (ListTodoCompleteTodo todos id') id' ≡ ListTodoCompleteTodo todos id'
ListTodoCompleteTodo-idem todos id' =
  begin
    ListTodoCompleteTodo (ListTodoCompleteTodo todos id') id'
  ≡⟨ {!   !} ⟩
    ListTodoCompleteTodo todos id'
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

CompleteAllTodos : ∀ {n} → (Vec Todo n) → (Vec Todo n)
CompleteAllTodos todos =
  v.map (λ todo →
    record todo { completed = true })
    todos

ListTodoCompleteAllTodos : (List Todo) → (List Todo)
ListTodoCompleteAllTodos todos =
  l.map (λ todo →
    record todo { completed = true })
    todos

ListTodoCompleteAllTodos-idem :
  (todos : List Todo) →
    ListTodoCompleteAllTodos (ListTodoCompleteAllTodos todos) ≡ ListTodoCompleteAllTodos todos
ListTodoCompleteAllTodos-idem todos = {!   !}

-- {-# COMPILE JS CompleteAllTodos =
--   function (todos) {
--     return todos.map(function(todo) {
--       todo.completed = true;
--       return todo;
--     });
--   }
-- #-}

VecTodoClearCompleted : ∀ {n} → (Vec Todo n) → (Vec Todo n)
VecTodoClearCompleted todos =
  padRight
    record
      { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
      ; completed = false
      ; text      = ""
      }
    (v.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)

ListTodoClearCompleted : (List Todo) → (List Todo)
ListTodoClearCompleted todos =
  (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)

ListTodoClearCompleted-idem :
  (todos : List Todo) →
      ListTodoClearCompleted (ListTodoClearCompleted todos) ≡ ListTodoClearCompleted todos
ListTodoClearCompleted-idem todos =
  filter-idem (λ e → dec-¬ (Todo.completed e Bool.≟ true)) todos

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
