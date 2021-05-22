# Janus: λ-calculus in Quantitative Type Theory

Janus is a small programming language examining the differences between additive
and multiplicities pairs in Quantitative Type Theory.

## Getting started

To run the Janus interpreter, make sure you have a recent enough `ghc` (8.10.x)
and `cabal` (3.4), then run:

    cabal build
    cabal run janusc

## Usage

Interpreter reads user's input, evaluates it, and prints the result in
an infinite loop. The input can either be a statement, see below, or a command.
Commands are identified by a leading colon. Some commands expect arguments,
which should follow the command. Janus interpreter supports the following
commands:

- `:load` takes a file path and it opens the file and evaluates its contents.
- `:browse` lists all the variables that are currently in scope, annotated with
their types.
- `:type` takes a Janus term and synthesises its type.
- `:quit` exits the interpreter.
- `:help`, or `:?` shows a short description of the interpreter's features.

For example, the following command loads the contents of the file `library.jns`:

<pre>
>>> :load library.jns
<i>... output produced by the evaluation of terms read from the file ...</i>
</pre>

### Statements

If no command is specified, interpreter expects the input to be a statement,
which is evaluated, and the result is printed out. Statements are:

- `assume` introduces new names and adds them to the context, subsequent Janus
terms will have these variables in scope.

<pre>
>>> assume (<i>usage</i> <i>name</i> : <i>term</i>) <i>...</i>
              │    │      │     │
              │    │      │     └─ Multiple variables can be added
              │    │      │        to context at the same time.
              │    │      └─────── Janus term which defines the type.
              │    └────────────── Name of the new variable.
              └─────────────────── Multiplicity of the variable.
                                   This is optional and when omitted,
                                   interpreter defaults to ω.
</pre>

- `let` defines a new variable and assigns it a result of evaluated Janus term.

<pre>
>>> let <i>usage</i> <i>name</i> = <i>term</i>
          │    │      │
          │    │      └─────────── Janus term which creates the value.
          │    └────────────────── Name of the new variable.
          └─────────────────────── Multiplicity of the variable.
                                   This is optional and when omitted,
                                   interpreter defaults to ω.
</pre>

- `eval` statement is a Janus expression which get evaluated and its result is
printed. `eval` has no effect on variables in scope.

<pre>
>>> <i>usage</i> <i>term</i>
      │    │
      │    └────────────────────── Janus term which creates the value.
      └─────────────────────────── Multiplicity of the result.
                                   This is optional and when omitted,
                                   interpreter defaults to ω.
</pre>

### An example of an interactive programming session

Declare a variable `A` of type *Universe* without a computational presence and
a linear variable `x` of type `A`:

    >>> assume (0 A : U) (1 x : A)
    0 A : 𝘜
    1 x : A

Define a variable `id` as an identity function. Its parameter `y` is a linear
variable, so the function body has to use it exactly once:

    >>> let 1 id = \x. \y. y : (0 x : 𝘜) -> (1 y : x) -> x
    1 id = (λx y. y) : ∀ (0 x : 𝘜) (1 y : x) . x

Examine the variable in scope using the `:browse` command:

    >>> :browse
    0 A : 𝘜
    1 x : A
    1 id : ∀ (0 x : 𝘜) (1 y : x) . x

Evaluate the identity function application:

    >>> 1 id A       -- Partially applied function, resulting in an identity function on type A.
    1 (λx. x) : (1 x : A) → A
    >>> 1 id A x     -- Fully applied function, resulting in the value of type A.
    1 x : A

As an example of incorrect term, we try to construct a pair of identity
functions. The variable `id` is however linear, so it can be used only once in
a term.

    >>> let 0 id_type = (0 x : 𝘜) -> (1 y : x) -> x : U     -- We define a helper variable to make
                                                            -- the terms more readable.
    0 id_type = (∀ (0 x : 𝘜) (1 y : x) . x) : 𝘜
    >>> let 1 pair = (id, id) : (_ : id_type) * id_type
    error: Mismatched multiplicities:
            id : ∀ (0 x : 𝘜) (1 y : x) . x
              Used ω-times, but available 1-times.

