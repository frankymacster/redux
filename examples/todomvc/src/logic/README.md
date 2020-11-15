### Objectives

The goals of this project are:
- to implement the ideas of https://arthurxavierx.github.io/ComonadsForUIs.pdf in Agda to manage the state of a web application
- to compile to js for use in the web application
- to use Agda to prove some propositions about abstractions used in the logic of the web application
- try first TodoMVC in Agda?

### Agda

#### Installation
https://agda.readthedocs.io/en/v2.6.1/getting-started/installation.html

#### References
- https://agda.readthedocs.io/en/v2.6.1/language/index.html
- https://plfa.github.io

### Javascript

#### to compile to a file to js:
```sh
agda --js --compile-dir=js todos.agda
```

#### to fix the imports

When compiling to js, Agda's js backend uses CommonJS and for some reason sets all imports to a module name (which refers only to `node_modules` modules). To fix this, we need to change the module imports to relative path imports. For example:
```js
require("./agda-rst.js") ---> require("./agda-rst.js")
```
Here is the bash command used to do this:
```sh
find . -type f -exec sed -i '' -e 's/require("\([a-zA-Z\.0-9-]*\)")/require(".\/\1.js")/g' {} \;
```

#### to create the bundled js file
```sh
browserify app-nodejs.js > bundle.js
```

### References
http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf
http://www.cse.chalmers.se/research/group/logic/book/book.pdf
https://agda.readthedocs.io/en/v2.6.1.1/language


-- AddTodo : (List Todo) → String → (List Todo)
-- AddTodo todos text =
--   todos ∷ʳ
--   record
--     { id        = 1 -- argmax (λ todo → λ e → e) todos) + 1
--     ; completed = false
--     ; text      = text
--     }

-- -- should add new element to list
-- AddTodoAddsNewListItem :
--   (todos : List Todo) (text : String) →
--     length (AddTodo todos text) ≡ length todos + 1
-- AddTodoAddsNewListItem todos text = length-++ todos
  -- begin
  --   length (AddTodo todos text)
  -- ≡⟨⟩
  --   length (todos ++ record { text = text ; completed = false ; id = 1 } ∷ [])
  -- ≡⟨ length-++ todos ⟩
  --   length todos + length (record { text = text ; completed = false ; id = 1 } ∷ [])
  -- ≡⟨⟩
  --   length todos + 1
  -- ∎