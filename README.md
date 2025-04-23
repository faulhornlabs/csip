

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
| `# indent quote`    | print the inner representation of the unindented source code |
| `# lex quote`       | print the token list |
| `# structure quote` | print the parse tree with whitespace |
| `# layout quote`    | print the parse tree |
| `# op quote`        | print the parse expression |
| `# exptree quote`   | print the parse expression with mixfix operators |
| `# sugar quote`     | print the desugared source code |
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

    csip show test/doc

If needed, the documentation is readable without the interactive mode:

    csip export test/doc | less -R

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

In csip, the representation of object code constructs is the same as the representation of user defined constructors.
There are no splice and quote operations.
Object code function applications and lambdas are inserted during converstion checking.
Object code lets are inserted during elaboration.
The staging algoritm is open normalization plus transformation of object code
applications, lambdas and lets to raw applications, lambdas and lets.


## Limitations and bugs

The following limitations and bugs are planned to be lifted:

- errors: check that no meta-level constructs remain in staged output
- errors: pattern matching should not be allowed on object language constructors
- staging feature: eta-expansion is needed on functions with object-level pattern matching only
- feature: deriving for Eq and Ord classes
- feature: only builtin modules can be imported

- feature: improve metavariable handling before pattern match compilation
- libraries: add typical dependently-typed data types (Fin, Vec, Dec, LessOrEqual, Image)

- feature: lookupDict should be deeply replaced
- feature: (=>) should be dependently typed
- feature: better representation for constructor applications (~>)
- feature: better handling of lambdas regarding type classes
- refactoring: superclasses -> coerce
- libraries: improve MTL

- printing: recursive definitions are not properly printed
- printing: sharing between values are sometimes lost during printing

- errors: add limitations for pretty-printed output
- errors: the main expression should be Code in staging mode
- errors: check validity of constructor types
- errors: check validity of type class and instance definitions
- missing documentation

- staging feature: add default interpreter backend
- staging feature: object level recursion compiled to object level constructs is not supported
- staging feature: support for multiple object codes
- staging feature: support for more stages (pattern matching on staging output)

- feature: support parametric modules

- feature: support pattern synonyms
- refactoring: Cons and Succ as pattern synonyms
- feature: elab-level (meta-meta-level) implementation of metalevel
  laziness, deriving, type classes, pattern synonyms, metavars, imports

- feautre: dot patterns (in dependent pattern matching) are not supported
- feature: support closed data types
- feature: support closed functions
- feature: support multi-parameter type classes
- feature: support local definitions
- feature: only simple guards are supported

- errors: infinite evaluation is not catched (by "gas", for example)
- parsing: multiline comments interferes with layout rules
- printing: string literal printing is not the inverse of the string literal parsing
- errors: better gluing result (show less generated code)
- errors: recursive meta solutions should not be allowed

- performance: faster parametric modules
- performance: type erasure
- performance: refactor String handling
- performance: optimize chained rewrite rules produced by pattern match compilation
- performance: parsing and pretty printing should be near linear time operation
- performance: faster supercombinator evaluation using interpreted register machines
- performance: run staging on closed meta level values
- performance: use linear maps (`IORef`s) instead of `IntMap`s

- staging feature: there is no stage polymorphism
- parsing: desugared `(a b : c)` does not share `c`
- feature: `import` acts as an "include"
- printing: types are not shown in elaborated output
- printing: implicit/explicit distinction of lambdas and applications are missing in elaborated output
- parsing: `do` and `where` should be at the end of the line
- parsing: user defined operator precedences are not supported
- performance: redirect graph nodes after conversion checking


## Performance

Implemented performance improvements:

- observable implicit sharing speeds up conversion checking and prevents sharing loss
- top level definitions are treated specially
- unsaturated and blocked rewrite rule applications are cached
- monad stacks in the Haskell source code are replaced with a custom solution



## Development workflows

The Csip cache can be cleaned with

    csip clean

The purpose of the clean command is to
remove unconsitent cache during development when needed.

### Main development workflow

    cabal repl
    > :main test
    <<< start_loop >>>
    <<< edit source files >>>
    > :reload
    > :main diff test
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
\a b -> ((a + b)^100 + b)^80
```

is compiled to

```haskell
\a b -> (do
    c = Add (do
          c = Add a b
          b_1 = Mul c (do
                b_1 = Mul c (Mul c c)
                b_2 = Mul b_1 b_1
                b_3 = Mul b_2 b_2
                Mul b_3 b_3
              )
          b_2 = Mul b_1 b_1
          Mul b_2 b_2
        ) b
    b_1 = Mul c (do
          b_1 = Mul c c
          Mul b_1 b_1
        )
    b_2 = Mul b_1 b_1
    b_3 = Mul b_2 b_2
    b_4 = Mul b_3 b_3
    Mul b_4 b_4
  )
```

given the definitions in [`test/staging/powerFast.csip`](test/staging/powerFast.csip)

and compiled to

```haskell
do
  sqr = \a -> Mul a a
  \v b -> sqr (sqr (sqr (sqr (do
              c = Add (sqr (sqr (do
                        c = Add v b
                        Mul c (sqr (sqr (sqr
                                (Mul c (sqr c))
                                )))))) b
              Mul c
                (sqr (sqr c))
            ))))
```

given the definitions in [`test/staging/powerFast2.csip`](test/staging/powerFast2.csip).

