open import Data.Bool as Bool using (Bool; false; true; if_then_else_)
open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≟_)
open import Data.List using (List; _∷ʳ_; filter; map)
open import Data.List.Extrema using (max)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary.Decidable using (⌊_⌋)

record Todo : Set where
  field
    text      : String
    completed : Bool
    id        : ℕ

AddTodo : (List Todo) → String → (List Todo)
AddTodo todos text =
  todos ∷ʳ
  record
    { id        = 1 -- change to state.reduce((maxId, todo) => Math.max(todo.id, maxId), -1) + 1,
    ; completed = false
    ; text      = text
    }

DeleteTodo : (List Todo) → ℕ → (List Todo)
DeleteTodo todos id' = filter (λ todo → Todo.id todo ≟ id') todos

EditTodo : (List Todo) → ℕ → String → (List Todo)
EditTodo todos id text =
  map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { text = text }
    else todo)
    todos

CompleteTodo : (List Todo) → ℕ → (List Todo)
CompleteTodo todos id =
  map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { completed = true }
    else todo)
    todos

CompleteAllTodos : (List Todo) → (List Todo)
CompleteAllTodos todos =
  map (λ todo →
    record todo { completed = true })
    todos

ClearCompleted : (List Todo) → (List Todo)
ClearCompleted todos =
  filter (λ todo → Bool._≟_ (Todo.completed todo) true) todos