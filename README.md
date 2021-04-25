# Janus

A λ-calculus interpreter with Quantitative Types and Additive Pairs

## Syntax

Here is the grammar for the language:

    Expr ::= let [Rig] Name = ITerm
           | [Rig] ITerm
           | assume Bindings

    Bindings ::= Binding Bindings | Binding

    Binding ::= ([Rig] Name : CTerm)

    CTerm ::= \ Name . CTerm                 -- Lambda abstraction
            | Binding -> CTerm               -- Pi type
            | (CTerm, CTerm)                 -- Multiplicative pair
            | Binding * CTerm                -- Tensor product type
            | <CTerm, CTerm>                 -- Additive pair
            | (Name : CTerm) & CTerm         -- With type
            | U                              -- Universe type
            | ()                             -- Multiplicative unit
            | I                              -- Multiplicative unit type
            | <>                             -- Additive unit
            | T                              -- Additive unit type
            | (CTerm)
            | ITerm

    ITerm ::= ITerm CTerm                    -- Lambda application
            | CTerm : CTerm                  -- Type annotation
            | Name                           -- Variable name
            | let Name @ Name, Name = ITerm in CTerm : CTerm
                                             -- Multiplicative pair eliminator
            | let Name @ () = ITerm in CTerm : CTerm
                                             -- Multiplicative unit eliminator
            | fst ITerm                      -- Additive pair eliminator
            | snd ITerm                      -- Additive pair eliminator
            | (ITerm)

    Rig ::= 0                                -- None
          | 1                                -- One
          | w                                -- Many

Multiplicity annotations specified as `[Rig]` are optional. `Many` is used if they are omitted. `Name`s are identifiers with the same format as in Haskell, which don't conflict with a reserved word.

## Credits

This project is based on the calculus described in _[A tutorial implementation of a dependently typed lambda calculus][]_.

[A tutorial implementation of a dependently typed lambda calculus]: https://www.andres-loeh.de/LambdaPi/
