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
open import Agda.Builtin.Nat public
  using () renaming (_==_ to _≡ᵇ_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_; cong₂; inspect; [_])
open import Data.Nat.Properties using (+-comm)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (does)
open import Data.Vec.Bounded.Base using (padRight; ≤-cast)
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary.Decidable.Core using (dec-false)
open import Function using (_∘_)
open import Data.List.Extrema ℕₚ.≤-totalOrder
open import Data.Empty using (⊥)

-- TODO add to std-lib
open import Relation.Nullary

dec-¬ : ∀ {a} {P : Set a} → Dec P → Dec (¬ P)
dec-¬ (yes p) = no λ prf → prf p
dec-¬ (no ¬p) = yes ¬p

-- TODO switch to Vec init?
allButLast : ∀ {a} {A : Set a} → List A → List A
allButLast []           = l.[]
allButLast (_ ∷ [])     = l.[]
allButLast (x ∷ x₁ ∷ l) = x l.∷ (allButLast (x₁ l.∷ l))

allButLast-∷ʳ : ∀ {a} {A : Set a} {l : List A} {x} → allButLast (l l.∷ʳ x) ≡ l
allButLast-∷ʳ {l = []}         = refl
allButLast-∷ʳ {l = _ ∷ []}     = refl
allButLast-∷ʳ {l = x ∷ x₁ ∷ l} = cong (x l.∷_) (allButLast-∷ʳ {l = x₁ l.∷ l})

filter' : {A : Set} → (A → Bool) → List A → List A
filter' p []               = l.[]
filter' p (x ∷ xs) with (p x)
...                | true  = x l.∷ filter' p xs
...                | false = filter' p xs


record Todo : Set where
  field
    text      : String
    completed : Bool
    id        : ℕ

-- can't define this for (List any) since (last []) must be defined for each carrier type
TodoListLast : List Todo → Todo
TodoListLast []          = record {}
TodoListLast (x ∷ [])    = x
TodoListLast (_ ∷ y ∷ l) = TodoListLast (y l.∷ l)




AddTodo : List Todo → String → List Todo
AddTodo todos text =
  todos l.∷ʳ
  record
    { id        = 1
    ; completed = false
    ; text      = text
    }

-- AddTodo is well-defined
AddTodoAddsNewListItem :
  (todos : List Todo) (text : String) →
    l.length (AddTodo todos text) ≡ l.length todos + 1
AddTodoAddsNewListItem todos text = length-++ todos

AddTodoSetsNewCompletedToFalse :
  (todos : List Todo) (text : String) →
    Todo.completed (TodoListLast (AddTodo todos text)) ≡ false
AddTodoSetsNewCompletedToFalse []          text = refl
AddTodoSetsNewCompletedToFalse (_ ∷ [])    text = refl
AddTodoSetsNewCompletedToFalse (_ ∷ _ ∷ l) text = AddTodoSetsNewCompletedToFalse (_ l.∷ l) text

-- TODO can't prove this until AddTodo definition changed
AddTodoSetsNewIdToNonExistingId :
  (todos : List Todo) (text : String) →
    l.length (l.filter (λ todo → dec-¬ (Todo.id todo ≟ Todo.id (TodoListLast (AddTodo todos text)))) (AddTodo todos text)) ≡ 1
AddTodoSetsNewIdToNonExistingId todos text = {!   !}

AddTodoSetsNewTextToText :
  (todos : List Todo) (text : String) →
    Todo.text (TodoListLast (AddTodo todos text)) ≡ text
AddTodoSetsNewTextToText []          text = refl
AddTodoSetsNewTextToText (_ ∷ [])    text = refl
AddTodoSetsNewTextToText (_ ∷ _ ∷ l) text = AddTodoSetsNewTextToText (_ l.∷ l) text

AddTodoDoesntChangeOtherTodos :
  (todos : List Todo) (text : String) →
    l.length todos > 0 →
      allButLast (AddTodo todos text) ≡ todos
AddTodoDoesntChangeOtherTodos (x l.∷ xs) text _<_ = allButLast-∷ʳ
-- END AddTodo is well-defined

-- TODO text1 ≠ text2
AddTodo-not-comm :
  (todos : List Todo) →
    (text1 : String) →
      (text2 : String) →
  (AddTodo (AddTodo todos text1) text2 ≢ AddTodo (AddTodo todos text2) text1)
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


DeleteTodo : (List Todo) → ℕ → (List Todo)
DeleteTodo todos id = l.filter (λ todo → dec-¬ (Todo.id todo ≟ id)) todos

DeleteTodo' : (List Todo) → ℕ → (List Todo)
DeleteTodo' todos id = filter' (λ todo → not (Todo.id todo ≡ᵇ id)) todos

DeleteTodo'RemoveTodoWithId :
  (todos : List Todo) (id : ℕ) →
    filter' (λ todo → Todo.id todo ≡ᵇ id) (DeleteTodo' todos id) ≡ l.[]
DeleteTodo'RemoveTodoWithId []       id = refl
DeleteTodo'RemoveTodoWithId (x ∷ xs) id with (Todo.id x ≡ᵇ id) | inspect (_≡ᵇ id) (Todo.id x)
... | true  | P.[ eq ]                  = DeleteTodo'RemoveTodoWithId xs id
... | false | P.[ eq ] rewrite eq       = DeleteTodo'RemoveTodoWithId xs id

-- TODO this one needs Todo to specify that it can only have one unique id
DeleteTodo'Removes1Element :
  (todos : List Todo) (id : ℕ) →
    l.length (DeleteTodo' todos id) ≡ l.length todos ∸ 1
DeleteTodo'Removes1Element []       id = refl
DeleteTodo'Removes1Element (x ∷ xs) id with (Todo.id x ≡ᵇ id) | inspect (_≡ᵇ id) (Todo.id x)
... | true  | P.[ eq ] rewrite eq = {!   !} -- DeleteTodo'Removes1Element xs id
... | false | P.[ eq ] rewrite eq = {!   !}

DeleteTodoDoesntChangeOtherTodos :
  (todos : List Todo) (id : ℕ) →
    DeleteTodo todos id ≡ l.filter (λ todo → dec-¬ (Todo.id todo ≟ id)) todos
DeleteTodoDoesntChangeOtherTodos todos id = refl
-- END DeleteTodo is well-defined

DeleteTodo-idem :
  (todos : List Todo) (id : ℕ) →
    DeleteTodo (DeleteTodo todos id) id ≡ DeleteTodo todos id
DeleteTodo-idem todos id = filter-idem (λ e → dec-¬ (Todo.id e ≟ id)) todos

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

EditTodo' : (List Todo) → ℕ → String → (List Todo)
EditTodo' todos id text =
  l.map (λ todo →
    if (Todo.id todo ≡ᵇ id)
    then record todo { text = text }
    else todo)
    todos

-- EditTodo is well-defined
-- EditTodoChangesText :
--   (todos : List Todo) (id : ℕ) (text : String) →
--     l.map Todo.text (l.filter (λ todo → Todo.id todo ≟ id) (EditTodo todos id text)) ≡ l.[ text ]
-- EditTodoChangesText todos id text = {!   !}

-- -- TODO not necessarily true
-- EditTodo'ChangesText :
--   (todos : List Todo) (id : ℕ) (text : String) →
--     l.map Todo.text (EditTodo' (filter' (λ todo → Todo.id todo ≡ᵇ id) todos) id text) ≡ l.map Todo.text (filter' (λ todo → Todo.id todo ≡ᵇ id) todos)
-- EditTodo'ChangesText []       id text = refl
-- EditTodo'ChangesText (x ∷ xs) id text with (Todo.id x ≡ᵇ id) | inspect (_≡ᵇ id) (Todo.id x)
-- ... | true  | P.[ eq ] rewrite eq = {!   !} -- cong (Todo.text x l.∷_) (EditTodo'ChangesText xs id text)
-- ... | false | P.[ eq ] rewrite eq = EditTodo'ChangesText xs id text

EditTodo'DoesntChangeId :
  (todos : List Todo) (id : ℕ) (text : String) →
    l.map Todo.id (EditTodo' todos id text) ≡ l.map Todo.id todos
EditTodo'DoesntChangeId []       id text = refl
EditTodo'DoesntChangeId (x ∷ xs) id text with (Todo.id x ≡ᵇ id)
... | true  = cong ((Todo.id x) l.∷_) (EditTodo'DoesntChangeId xs id text)
... | false = cong ((Todo.id x) l.∷_) (EditTodo'DoesntChangeId xs id text)

EditTodo'DoesntChangeCompleted :
  (todos : List Todo) (id : ℕ) (text : String) →
    l.map Todo.completed (EditTodo' todos id text) ≡ l.map Todo.completed todos
EditTodo'DoesntChangeCompleted []       id text = refl
EditTodo'DoesntChangeCompleted (x ∷ xs) id text with (Todo.id x ≡ᵇ id)
... | true  = cong ((Todo.completed x) l.∷_) (EditTodo'DoesntChangeCompleted xs id text)
... | false = cong ((Todo.completed x) l.∷_) (EditTodo'DoesntChangeCompleted xs id text)

EditTodo'DoesntChangeOtherTodos :
  (todos : List Todo) (id : ℕ) (text : String) →
    filter' (λ todo → not (Todo.id todo ≡ᵇ id)) (EditTodo' todos id text) ≡ filter' (λ todo → not (Todo.id todo ≡ᵇ id)) todos
EditTodo'DoesntChangeOtherTodos []       id text = refl
EditTodo'DoesntChangeOtherTodos (x ∷ xs) id text with (Todo.id x ≡ᵇ id) | inspect (_≡ᵇ id) (Todo.id x)
... | true  | P.[ eq ] rewrite eq = EditTodo'DoesntChangeOtherTodos xs id text
... | false | P.[ eq ] rewrite eq = cong (x l.∷_) (EditTodo'DoesntChangeOtherTodos xs id text)

EditTodoLengthUnchanged :
  (todos : List Todo) (id' : ℕ) (text : String) →
    l.length (EditTodo todos id' text) ≡ l.length todos
EditTodoLengthUnchanged todos id' text = length-map (λ todo → if (⌊ Todo.id todo ≟ id' ⌋) then record todo { text = text } else todo) todos
-- END EditTodo is well-defined

EditTodo'-idem :
  (todos : List Todo) (id : ℕ) (text : String) →
    EditTodo' (EditTodo' todos id text) id text ≡ EditTodo' todos id text
EditTodo'-idem []       id text = refl
EditTodo'-idem (x ∷ xs) id text with (Todo.id x ≡ᵇ id) | inspect (_≡ᵇ id) (Todo.id x)
... | true  | P.[ eq ] rewrite eq = cong (record x { text = text } List.∷_) (EditTodo'-idem xs id text)
... | false | P.[ eq ] rewrite eq = cong (x List.∷_) (EditTodo'-idem xs id text)

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

CompleteTodo' : (List Todo) → ℕ → (List Todo)
CompleteTodo' todos id =
  l.map (λ todo →
    if (Todo.id todo ≡ᵇ id)
    then record todo { completed = true }
    else todo)
    todos

-- CompleteTodo is well-defined
-- TODO don't know if there is only one instance of Todo with that id
CompleteTodo'ChangesCompleted :
  (todos : List Todo) (id : ℕ) →
    l.map Todo.completed (filter' (λ todo → Todo.id todo ≡ᵇ id) (CompleteTodo' todos id)) ≡ l.map (λ todo → true) (filter' (λ todo → Todo.id todo ≡ᵇ id) todos)
CompleteTodo'ChangesCompleted []       id = refl
CompleteTodo'ChangesCompleted (x ∷ xs) id with Todo.id x ≡ᵇ id | inspect (_≡ᵇ id) (Todo.id x)
... | true  | P.[ eq ] rewrite eq = cong (true l.∷_) (CompleteTodo'ChangesCompleted xs id)
... | false | P.[ eq ] rewrite eq = CompleteTodo'ChangesCompleted xs id

CompleteTodoDoesntChangeIds :
  (todos : List Todo) (id : ℕ) →
    l.map Todo.id (CompleteTodo todos id) ≡ l.map Todo.id todos
CompleteTodoDoesntChangeIds []       id = refl
CompleteTodoDoesntChangeIds (x ∷ []) id = cong (l._∷ l.[]) (helper x id)
  where
    helper :
      (x : Todo) (id : ℕ) →
        Todo.id (if ⌊ Todo.id x ≟ id ⌋ then record { text = Todo.text x ; completed = true ; id = Todo.id x } else x) ≡ Todo.id x
    helper x id with (⌊ Todo.id x ≟ id ⌋)
    ...         | true  = refl
    ...         | false = refl
CompleteTodoDoesntChangeIds (x ∷ xs) id =
  begin
    l.map Todo.id (CompleteTodo (x l.∷ xs) id)
  ≡⟨⟩
    (l.map Todo.id (CompleteTodo l.[ x ] id)) l.++ l.map Todo.id (CompleteTodo xs id)
  ≡⟨ cong (l._++ l.map Todo.id (CompleteTodo xs id)) (CompleteTodoDoesntChangeIds (x l.∷ l.[]) id) ⟩
    l.map Todo.id (l.[ x ]) l.++ l.map Todo.id (CompleteTodo xs id)
  ≡⟨⟩
    l.[ Todo.id x ] l.++ l.map Todo.id (CompleteTodo xs id)
  ≡⟨⟩
    Todo.id x l.∷ l.map Todo.id (CompleteTodo xs id)
  ≡⟨ cong (Todo.id x l.∷_) (CompleteTodoDoesntChangeIds xs id) ⟩
    Todo.id x l.∷ l.map Todo.id xs
  ≡⟨⟩
    l.map Todo.id (x l.∷ xs)
  ∎

CompleteTodoDoesntChangeText :
  (todos : List Todo) (id : ℕ) →
    l.map Todo.text (CompleteTodo todos id) ≡ l.map Todo.text todos
CompleteTodoDoesntChangeText []       id = refl
CompleteTodoDoesntChangeText (x ∷ []) id = cong (l._∷ l.[]) (helper x id)
  where
    helper :
      (x : Todo) (id : ℕ) →
        Todo.text (if ⌊ Todo.id x ≟ id ⌋ then record { text = Todo.text x ; completed = true ; id = Todo.id x } else x) ≡ Todo.text x
    helper x id with (⌊ Todo.id x ≟ id ⌋)
    ...         | true  = refl
    ...         | false = refl
CompleteTodoDoesntChangeText (x ∷ xs) id =
  begin
    l.map Todo.text (CompleteTodo (x l.∷ xs) id)
  ≡⟨⟩
    (l.map Todo.text (CompleteTodo l.[ x ] id)) l.++ l.map Todo.text (CompleteTodo xs id)
  ≡⟨ cong (l._++ l.map Todo.text (CompleteTodo xs id)) (CompleteTodoDoesntChangeText (x l.∷ l.[]) id) ⟩
    l.map Todo.text (l.[ x ]) l.++ l.map Todo.text (CompleteTodo xs id)
  ≡⟨⟩
    l.[ Todo.text x ] l.++ l.map Todo.text (CompleteTodo xs id)
  ≡⟨⟩
    Todo.text x l.∷ l.map Todo.text (CompleteTodo xs id)
  ≡⟨ cong (Todo.text x l.∷_) (CompleteTodoDoesntChangeText xs id) ⟩
    Todo.text x l.∷ l.map Todo.text xs
  ≡⟨⟩
    l.map Todo.text (x l.∷ xs)
  ∎

CompleteTodo'DoesntChangeOthersCompleted :
  (todos : List Todo) (id : ℕ) →
    l.map Todo.completed (CompleteTodo' (filter' (λ todo → not (Todo.id todo ≡ᵇ id)) todos) id) ≡ l.map Todo.completed (filter' (λ todo → not (Todo.id todo ≡ᵇ id)) todos)
CompleteTodo'DoesntChangeOthersCompleted []       id = refl
CompleteTodo'DoesntChangeOthersCompleted (x ∷ xs) id with Todo.id x ≡ᵇ id | inspect (_≡ᵇ id) (Todo.id x)
... | true  | P.[ eq ] rewrite eq = CompleteTodo'DoesntChangeOthersCompleted xs id -- 
... | false | P.[ eq ] rewrite eq = cong (Todo.completed x l.∷_) (CompleteTodo'DoesntChangeOthersCompleted xs id)

CompleteTodoLengthUnchanged :
  (todos : List Todo) (id : ℕ) →
    l.length (CompleteTodo todos id) ≡ l.length todos
CompleteTodoLengthUnchanged todos id = length-map (λ todo → if (⌊ Todo.id todo ≟ id ⌋) then record todo { completed = true } else todo) todos
-- END CompleteTodo is well-defined

CompleteTodo'-idem :
  (todos : List Todo) (id : ℕ) →
    CompleteTodo' (CompleteTodo' todos id) id ≡ CompleteTodo' todos id
CompleteTodo'-idem []       id = refl
CompleteTodo'-idem (x ∷ xs) id with Todo.id x ≡ᵇ id | inspect (_≡ᵇ id) (Todo.id x)
... | true  | P.[ eq ] rewrite eq = cong (record x { completed = true } l.∷_) (CompleteTodo'-idem xs id)
... | false | P.[ eq ] rewrite eq = cong (x l.∷_) (CompleteTodo'-idem xs id)

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

-- CompleteAllTodos is well-defined
CompleteAllTodosAllCompleted :
  (todos : List Todo) →
    l.filter (λ todo → (Todo.completed todo) Bool.≟ false) (CompleteAllTodos todos) ≡ l.[]
CompleteAllTodosAllCompleted []       = refl
CompleteAllTodosAllCompleted (x ∷ xs) = CompleteAllTodosAllCompleted xs

CompleteAllTodosDoesntChangeIds :
  (todos : List Todo) →
    l.map Todo.id (CompleteAllTodos todos) ≡ l.map Todo.id todos
CompleteAllTodosDoesntChangeIds []       = refl
CompleteAllTodosDoesntChangeIds (x ∷ []) = cong (l._∷ l.[]) (helper x)
  where
    helper :
      (x : Todo) →
        Todo.id (record x { completed = true }) ≡ Todo.id x
    helper x = refl
CompleteAllTodosDoesntChangeIds (x ∷ xs) =
  begin
    l.map Todo.id (CompleteAllTodos (x l.∷ xs))
  ≡⟨⟩
    (l.map Todo.id (CompleteAllTodos l.[ x ])) l.++ l.map Todo.id (CompleteAllTodos xs)
  ≡⟨ cong (l._++ l.map Todo.id (CompleteAllTodos xs)) (CompleteAllTodosDoesntChangeIds (x l.∷ l.[])) ⟩
    l.map Todo.id (l.[ x ]) l.++ l.map Todo.id (CompleteAllTodos xs)
  ≡⟨⟩
    l.[ Todo.id x ] l.++ l.map Todo.id (CompleteAllTodos xs)
  ≡⟨⟩
    Todo.id x l.∷ l.map Todo.id (CompleteAllTodos xs)
  ≡⟨ cong (Todo.id x l.∷_) (CompleteAllTodosDoesntChangeIds xs) ⟩
    Todo.id x l.∷ l.map Todo.id xs
  ≡⟨⟩
    l.map Todo.id (x l.∷ xs)
  ∎

CompleteAllTodosDoesntChangeText :
  (todos : List Todo) →
    l.map Todo.text (CompleteAllTodos todos) ≡ l.map Todo.text todos
CompleteAllTodosDoesntChangeText []       = refl
CompleteAllTodosDoesntChangeText (x ∷ []) = cong (l._∷ l.[]) (helper x)
  where
    helper :
      (x : Todo) →
        Todo.text (record x { completed = true }) ≡ Todo.text x
    helper x = refl
CompleteAllTodosDoesntChangeText (x ∷ xs) =
  begin
    l.map Todo.text (CompleteAllTodos (x l.∷ xs))
  ≡⟨⟩
    (l.map Todo.text (CompleteAllTodos l.[ x ])) l.++ l.map Todo.text (CompleteAllTodos xs)
  ≡⟨ cong (l._++ l.map Todo.text (CompleteAllTodos xs)) (CompleteAllTodosDoesntChangeText (x l.∷ l.[])) ⟩
    l.map Todo.text (l.[ x ]) l.++ l.map Todo.text (CompleteAllTodos xs)
  ≡⟨⟩
    l.[ Todo.text x ] l.++ l.map Todo.text (CompleteAllTodos xs)
  ≡⟨⟩
    Todo.text x l.∷ l.map Todo.text (CompleteAllTodos xs)
  ≡⟨ cong (Todo.text x l.∷_) (CompleteAllTodosDoesntChangeText xs) ⟩
    Todo.text x l.∷ l.map Todo.text xs
  ≡⟨⟩
    l.map Todo.text (x l.∷ xs)
  ∎

CompleteAllTodosLengthUnchanged :
  (todos : List Todo) →
    l.length (CompleteAllTodos todos) ≡ l.length todos
CompleteAllTodosLengthUnchanged todos = length-map (λ todo → record todo { completed = true }) todos
-- END CompleteAllTodos is well-defined

-- CompleteAllTodos-idem

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

-- ClearCompleted is well-defined
ClearCompletedRemovesOnlyCompleted :
  (todos : List Todo) →
    l.map Todo.completed (ClearCompleted todos) ≡ l.map Todo.completed (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedRemovesOnlyCompleted todos = refl

ClearCompletedDoesntChangeCompleted :
  (todos : List Todo) →
    l.map Todo.completed (ClearCompleted todos) ≡ l.map Todo.completed (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedDoesntChangeCompleted todos = refl

ClearCompletedDoesntChangeIds :
  (todos : List Todo) →
    l.map Todo.id (ClearCompleted todos) ≡ l.map Todo.id (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedDoesntChangeIds todos = refl

ClearCompletedDoesntChangeText :
  (todos : List Todo) →
    l.map Todo.text (ClearCompleted todos) ≡ l.map Todo.text (l.filter (λ todo → dec-¬ ((Todo.completed todo) Bool.≟ true)) todos)
ClearCompletedDoesntChangeText todos = refl
-- END ClearCompleted is well-defined

ClearCompleted-idem :
  (todos : List Todo) →
    ClearCompleted (ClearCompleted todos) ≡ ClearCompleted todos
ClearCompleted-idem todos = filter-idem (λ e → dec-¬ (Todo.completed e Bool.≟ true)) todos

-- {-# COMPILE JS ClearCompleted =
--   function (todos) {
--     return todos.filter(function(todo) {
--       return !todo.completed;
--     });
--   }
-- #-}

-- interactions
-- AddTodo-AddTodo
-- DeleteTodo-DeleteTodo
-- AddTodo-DeleteTodo
-- DeleteTodo-AddTodo
-- EditTodo-EditTodo
-- AddTodo-EditTodo
-- EditTodo-AddTodo
-- ...
