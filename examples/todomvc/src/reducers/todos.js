import {
  ADD_TODO,
  DELETE_TODO,
  EDIT_TODO,
  COMPLETE_TODO,
  COMPLETE_ALL_TODOS,
  CLEAR_COMPLETED
} from '../constants/ActionTypes'

import {
  AddTodo,
  DeleteTodo,
  EditTodo,
  CompleteTodo,
  CompleteAllTodos,
  ClearCompleted
} from '../logic/js/jAgda.todos.js'

const initialState = [
  {
    text: 'Use Redux',
    completed: false,
    id: 0
  }
]

export default function todos(state = initialState, action) {
  switch (action.type) {
    case ADD_TODO:
      return AddTodo(state)(action.text)

    case DELETE_TODO:
      return DeleteTodo(state)(action.id)

    case EDIT_TODO:
      return EditTodo(state)(action.id)(action.text)

    case COMPLETE_TODO:
      return CompleteTodo(state)(action.id)

    case COMPLETE_ALL_TODOS:
      return CompleteAllTodos(state)

    case CLEAR_COMPLETED:
      return ClearCompleted(state)

    default:
      return state
  }
}
