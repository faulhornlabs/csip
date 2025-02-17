

Csip is a minimalistic Agda-like language for writing efficient programs
with high-level abstractions.

Compared to Agda, Csip can do staged compilation, it does not have termination checking
and it has a minimal but practical set of language features.

Warning: It is not advised to use Csip yet, it is under development.


## Installation

1.  Install the GHC Haskell compiler with [ghcup](https://www.haskell.org/ghcup/).
2.  Execute the following command:

        cabal install


## Basic usage

The extension of Csip source files is `.csip`  

The first lines of `.csip` files are directives
which tell the compiler what to do.  
Main directives:

| Directive           | Description |
| ---                 | ---         |
| `# source`          | print the source code |
| `# source quote`    | print the inner representation of the source code |
| `# indent quote`    | print the inner representation of the unidented source code |
| `# lex quote`       | print the token list |
| `# structure quote` | print the parse tree with whitespace |
| `# layout quote`    | print the parse tree |
| `# op quote`        | print the parse expression |
| `# exptree quote`   | print the parse expression with mixfix operators |
| `# sugar quote`     | print the desugared source code |
| `# scope quote`     | print the scope checked source code |
| `# elab`            | print the elaborated main expression |
| `# eval`            | print the normalized main expression |
| `# stage`           | print the staged main expression |
| `# haskell_stage`   | print the staged main expression parsable with Haskell Read instance |


### Compilation

Compilation of source files:

    csip FILE|DIR

The output is written to the standard output.  

Note that the compiler output is cached.


### Interactive mode

Interactive compilation of source files:

    csip show FILE|DIR

Available commands in interactive mode:

| Keystroke | Description |
| ---       | ---         |
| `q`       | exit        |
| `r`       | reload      |
| Up, Down, PageUp, PageDown | scroll window |
| Left, Right | navigate between files |


## Documentation

You can read the documentation of Csip (currently only about the syntactic frontend) with

    csip show csip/doc

If needed, the documentation is readable without the interactive mode:

    csip export csip/doc | less -R

## Features

### Syntax

Key features:

- The parser and pretty printer is a composition of bidirectional nanopasses.
  The data between nanopasses is inspectable with compiler directives.
- Csip's syntax is defined entirely by an operator precedence grammar.
  The parsing and pretty printing algorithms used work for any operator grammar.
- No semicolons are needed at the end of definitions (layout rules are supported).
- Syntax sugaring is bidirectional too.
- Source code locations are encapsulated in a custom `String` data structure.
  There is no need to store and carry source code locations otherwise.
  Highlighted error messages are derived from the custom `String` data.


### Elaboration

The dependent typechecking algorithm is based on Coquand's algorithm,
as implemented in [András Kovács's elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).  
Possible differences:

- Csip uses globally unique names instead of De Bruijn indices.  
  Indices are still used in supercombinators (lifted lambda bodies).
- Csip's value representation uses observable implicit sharing.  
  Implicit sharing of Haskell is made visible by adding unique identifiers
  (names) to each node of the value graph.
  An important invariant is that if the identifiers of two nodes are
  equal then the two nodes are equal. This invariant is used
  to speed up conversion checking.
- The explicit/implicit distinction of lambdas and applications are erased in terms and values,
  for efficiency. This information can be recovered after elaboration from
  the explicit/implicit distinction of Pi types.
- Terms may contain closed values.
- There is a dedicated consturctor for terms generated during elaboration.
- Forced flexible values are destructively updated.
- Forcing of flexible values is speeded up by caching the main blocking metavariable
  in flexible values.  
  If the main metavariable is solved, forcing results in a rigid value
  or a flexible value with the next main blocking metavariable.
- Glued representation is implemented currently with an extra constructor for values.
- Algebraic data types are also supported.

### Implementation details of algebraic data types

- Currently all data types and functions are open, which means
  that type constructors, data constructors and function alternatives
  can be given in any order obeying dependency.
- Type checking of functions alternatives happens separately for the left hand side
  and the right hand side. There is no need to compile pattern matching to eliminators
  and generate types for eliminators for typechecking.
- Function alternatives are interpreted as rewrite rules.
- Rewrite rules are compiled to conditional expressions branching on constructor tags
  and projections to access the arguments of constructors.
- Rewrite rules of the same function are chained together, i.e.
  if the left hand side of a rule does not match, the next rule of the same function is tried
  (not *all* rewrite rules are tried).
- The right hand sides of the rewrite rules are marked.
  Rewrite rule application is successful only if the right hand side is reached.


### Staging

Staged compilation is defined in [András Kovács's staged repository](https://github.com/AndrasKovacs/staged).

Currently Csip implements a shallow form of staging;
object code function type constructors, applications, lambdas and lets are
inserted during elaboration. There are no splice and quote operations.
The staging algoritm is open normalization plus transformation of object code
applications, lambdas and lets to raw applications, lambdas and lets.



## Limitations and bugs

The following limitations and bugs are planned to be lifted:

- type classes are not supported
- top level object language lets should be at the end
- pattern matching compiled to object level constructs is not supported
- object level recursion compiled to object level constructs is not supported
- there is no module system
- foralls for functions and constructors should be explicitly given
- no support for multiple object codes
- missing check that pattern matching is not allowed on object language constructors
- missing check that the main expression should be Code in staging mode
- local definitions are not supported
- local do notation is not supported
- recursive definitions are not properly printed
- closed data types and closed functions are not supported
- sharing between values are sometimes lost during printing
- types are not shown in printed output
- implicit/explicit distinction of lambdas and applications are missing
- multiline comments interferes with layout rules
- string literal printing is not the inverse of the string literal parsing
- desugared `(a b : c)` does not share `c`
- user defined operator precedences are not supported


## Performance

Implemented performance improvements:

- observable implicit sharing speeds up conversion checking
  and prevents sharing loss
- unsaturated and blocked rewrite rule applications are cached
- monad stacks in the Haskell source code are replaced with a custom solution

Planned performance improvements:

- optimize chained rewrite rules produced by pattern match compilation
- fast head of spine access in terms and values
- run staging on closed meta level values
- identify names with `Int`s
- use `IntMap`s instead of `Map`s
- use linear maps (`IORef`s) instead of `IntMap`s
- redirect graph nodes after conversion checking
- parsing and pretty printing should be near linear time operation
- faster supercombinator evaluation using interpreted register machines
- use `Strict` pragma and `UNPACK` pragmas in the Haskell source files


## Development workflows

The Csip cache can be cleaned with

    csip clean

The purpose of the clean command is to
remove unconsitent cache during development when needed.

### Main development workflow

    cabal repl
    > :main csip
    <<< start_loop >>>
    <<< edit source files >>>
    > :reload
    > :main diff csip
    <<< goto start_loop >>>


### Performance improvement workflow

    cabal install
    csip .
    time csip diff .
    <<< start_loop >>>
    <<< edit source files >>>
    cabal install
    time csip diff .
    <<< goto start_loop >>>


## Examples

```haskell
\a b -> ((a + b)^5 + b)^10
```

is compiled to

```haskell
\a b -> (do
    c = Add a b
    b_1 = Mul c c
    c_1 = Add
      (Mul c (Mul b_1 b_1))
      b
    b_2 = Mul c_1 c_1
    b_3 = Mul c_1 (Mul b_2 b_2)
    Mul b_3 b_3
  )
```

given the definitions in [`csip/staging/powerFast.csip`](csip/staging/powerFast.csip).

