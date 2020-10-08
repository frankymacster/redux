open import Data.Bool as Bool using (Bool; false; true; if_then_else_)
open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List; _∷ʳ_; filter; map; length)

record Todo : Set where
  field
    text      : String
    completed : Bool
    id        : ℕ

AddTodo : (List Todo) → String → (List Todo)
AddTodo todos text =
  todos ∷ʳ
  record
    { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
    ; completed = false
    ; text      = text
    }

{-# COMPILE JS AddTodo =
  function (todos, text) {
    return [
        ...todos,
        {
          id: todos.reduce((maxId, todo) => Math.max(todo.id, maxId), -1) + 1,
          completed: false,
          text: text
        }
      ]
  }
#-}

DeleteTodo : (List Todo) → ℕ → (List Todo)
DeleteTodo todos id' = filter (λ todo → Todo.id todo ≟ id') todos

{-# COMPILE JS DeleteTodo =
  function (todos, id) {
    return todos.filter(todo =>
      todo.id !== id
    )
  }
#-}

EditTodo : (List Todo) → ℕ → String → (List Todo)
EditTodo todos id text =
  map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { text = text }
    else todo)
    todos

{-# COMPILE JS EditTodo =
  function (todos, id, text) {
    return todos.map(todo =>
        todo.id === id ?
          { ...todo, text } :
          todo
      )
  }
#-}

CompleteTodo : (List Todo) → ℕ → (List Todo)
CompleteTodo todos id =
  map (λ todo →
    if (⌊ Todo.id todo ≟ id ⌋)
    then record todo { completed = true }
    else todo)
    todos

{-# COMPILE JS CompleteTodo =
  (todos, id) =>
    todos.map(todo =>
      todo.id === id ?
        { ...todo, completed: !todo.completed } :
        todo
    )
#-}

CompleteAllTodos : (List Todo) → (List Todo)
CompleteAllTodos todos =
  map (λ todo →
    record todo { completed = true })
    todos

{-# COMPILE JS CompleteAllTodos =
  (todos) => {
    const areAllMarked = state.every(todo => todo.completed)
    return todos.map(todo => ({
      ...todo,
      completed: !areAllMarked
    }))
  }
#-}

ClearCompleted : (List Todo) → (List Todo)
ClearCompleted todos =
  filter (λ todo → Bool._≟_ (Todo.completed todo) true) todos

{-# COMPILE JS ClearCompleted =
  (todos) =>
    todos.filter(todo => todo.completed === false)
#-}

-- add-todos-length-increased-by-1 : ∀ (todos : List Todo) → length (AddTodo todos "test")
-- add-todos-length-increased-by-1 = ?
-- delete-todos-length-decreased-by-1-except-if-length-0 : ()
-- edit-todos-length-not-changed : ()
-- complete-todos-length-not-changed : ()
-- complete-all-todos-length-not-changed : ()

-- clear-completed-todos-not-have-completed : ()

-- should not generate duplicate ids after CLEAR_COMPLETE
