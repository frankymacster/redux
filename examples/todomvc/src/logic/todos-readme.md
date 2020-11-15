~~-- operations ~~
~~  -- AddTodo ~~
~~  -- DeleteTodo ~~
~~  -- CompleteTodo ~~
~~  -- ClearCompleted ~~
~~  -- CompleteAllTodos ~~

~~-- horizontal properties ~~
~~  -- AddTodo ~~
~~  --   non-commutative ~~
~~  -- DeleteTodo ~~
~~  --   idempotent ~~
~~  -- CompleteTodo ~~
~~  --   idempotent ~~
~~  -- ClearCompleted ~~
~~  --   idempotent ~~
~~  -- CompleteAllTodos ~~
~~  --   idempotent ~~
~~  -- EditTodo ~~
~~  --   EditTodo - EditTodo Todo list length doesn't change ~~

~~-- vertical properties ~~
~~  -- AddTodo ~~
~~  --   AddTodoSetsNewCompletedToFalse ~~
~~  --   AddTodoSetsNewIdToNonExistingId ~~
~~  --   AddTodoSetsNewTextToText ~~
~~  --   doesn't change id of other Todos ~~
~~  --   doesn't change text of other Todos ~~
~~  --   doesn't change completed of other Todos ~~
~~  -- DeleteTodo ~~
~~  --   DeleteTodoRemoveTodoWithId ~~
~~  --   DeleteTodoRemoves1Element ~~
~~  --     only way to add todo is with AddTodo and AddTodo gives non existing id to new todo ~~
~~  --   doesn't change id of other Todos ~~
~~  --   doesn't change text of other Todos ~~
~~  --   doesn't change completed of other Todos ~~
~~  -- CompleteTodo ~~
~~  --   CompleteTodoSetsTodoWithIdCompletedToTrue ~~
~~  --   doesn't touch any other Todo ~~
~~  --   doesn't change id of any Todo ~~
~~  --   doesn't change text of any Todo ~~
~~  -- ClearCompleted ~~
~~  --   doesn't remove Todos where completed = false ~~
~~  --   doesn't change id of false Todo ~~
~~  --   doesn't change completed of false Todo ~~
~~  --   doesn't change text of false Todo ~~
~~  -- CompleteAllTodos ~~
~~  --   all Todos have completed = true ~~
~~  --   doesn't change id of any Todo ~~
~~  --   doesn't change text of any Todo ~~
~~  -- EditTodo ~~
~~  --   modifies Todo with given id's text ~~
~~  --   doesn't change the id ~~
~~  --   doesn't change completed ~~
~~  --   doesn't modify other Todos ~~