

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
- Source code locations are encapsulated in a custom String data structure.
  There is no need to store and carry source code locations otherwise.
  Highlighted error messages are derived from the custom String data.


### Elaboration

The dependent typechecking algorithm is based on Coquand's algorithm,
as implemented in [András Kovács's elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).  
Differences:

- Csip uses globally unique names instead of De Bruijn indices  
  (indices are still used in fully bound lambda bodies).
- Csip's value representation uses observable implicit sharing.  
  Implicit sharing of Haskell is made visible by adding unique identifiers
  (names) to each nodes of the value graph.
  An important invariant is that if the identifiers of two nodes are
  equal then the two nodes are equal. This invariant is used
  to speed up conversion checking.
- The explicit/implicit distinction of lambdas and applications are erased in terms and values,
  for efficiency. This information can be recovered after elaboration from
  the explicit/implicit distinction of Pi types.
- Terms may contain closed values.
- There is a dedicated consturctor for generated terms.
  (Terms are generated for holes.)
- Forcing of flexible values is speeded up by caching the main blocking metavariable
  in flexible values.  
  If the main metavariable is solved, forcing results in a rigid value
  or a flexible value with the next main blocking metavariable.
- Glued representation is implemented currently with an extra constructor for values.

Algebraic data types are also supported in the following way:

- Currently type constructors, data constructors and function alternatives
  can be given in any order obeying dependency.
  This means that data types and functions are open.
- Type checking of functions alternatives happens separately for the left hand side
  and the right hand side. There is no need to compile pattern matching to eliminators
  and generate types for eliminators for typechecking.
- Function alternatives are compiled to rewrite rules.
- Rewrite rules are compiled to terms containing tag-checking conditional expressions
  and selector functions to access the arguments of constructors.
- Rewrite rules of the same function are chained together, i.e.
  if the left hand side of a rule does not match, the next rule of the same function is tried.
  (no need to check *all* rewrite rules).
  Note that the chained expression is not yet optimized.
- The right hand sides of the rewrite rules are marked.
  Unsaturated and blocked rewrite rule applications are cached.


### Staging

Staged compilation is defined in [András Kovács's staged repository](https://github.com/AndrasKovacs/staged).

Currently Csip implements a shallow form of staging;
object code function type constructors, applications, lambdas and lets are
inserted during elaboration. There are no splice and quote operations.
The staging algoritm is normalization plus transformation of object code
applications, lambdas and lets to raw applications, lambdas and lets.



## Limitations

The following limitations are planned to be lifted:

- syntax
  - local do notation is not yet supported
  - multiline comments interferes with layout rules;  
    the solution is to move the indent pass after the comments pass
  - the inverse of the string pass is missing
  - desugared `(a b : c)` does not share `c`
- printing of terms and values
  - types are missing
  - implicit/explicit distinction of lambdas and applications are missing
  - sharing between values are sometimes lost
  - recursive lets are not properly printed
- unification
  - no pruning
  - currently flexible values cannot be refined to Pi types
- algebraic data types
  - implict arguments in rules should be explicit
  - local definitions are not supported
- staging
  - top level object language lets should be at the end
  - object functions should be eta-expanded

## Bugs

There are lots of minor bugs, mostly missing validity checks.


## Performance

Adding features (like supporting type classes) is preferred before
performance improvements.

Implemented performance improvements:

- monad stacks are replaced with a custom solution
- observable implicit sharing speeds up conversion checking
  and prevents sharing loss

Planned performance improvements:

- run staging on closed meta level values
- identify names with `Int`s
- use `IntMap`s instead of `Map`s
- use linear maps (`IORef`s) instead of `IntMap`s
- redirect graph nodes after conversion checking
- parsing and pretty printing should be near linear time operation
- fast head of spine access in terms and values
- optimize pattern match compilation
- faster supercombinator evaluation using interpreted register machines
- use Strict pragma and UNPACK pragmas


## Development workflows

The Csip cache can be cleaned with

    csip clean

The purpose of the clean command is to
remove unconsitent cache during development (when needed).

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


## Example

Content of [csip/staging/powerFast.csip](csip/staging/powerFast.csip):

```haskell
# stage

// builtins
Ty   : Type
Code : Ty -> Type
Arr  : Ty -> Ty -> Ty
Lam  : {a b} -> (Code a -> Code b) -> Code (Arr a b)
App  : {a b} -> Code (Arr a b) -> Code a -> Code b
Let  : {a b} -> Code a -> (Code a -> Code b) -> Code b
Succ : Nat -> Nat
// end of builtins

Parity : Type
Even : Parity
Odd  : Parity

Half : Type
MkHalf : Parity -> Nat -> Half

half : Nat -> Half
half 0 = MkHalf Even 0
half 1 = MkHalf Odd  0
half (Succ (Succ (half --> MkHalf p n))) = MkHalf p (Succ n)

// object code types and functions (foreign function interface)
Int :: Type
One :: Int
Mul :: Int -> Int -> Int

sqr : Code Int -> Code Int
    = \a -> (b := a; Mul b b)

power : Nat -> Code Int -> Code Int
power 1 a = a
power 0 a = One
power (half --> MkHalf Even k) a =        sqr (power k a)
power (half --> MkHalf Odd  k) a = Mul a (sqr (power k a))

power5 := \a -> power 5 a

\a -> power5 (power5 a)
```

Output of `csip csip/staging/powerFast.csip`:

```haskell
do
  power5 = \a -> (do
        b = Mul a a
        Mul a (Mul b b)
      )
  \a -> power5 (power5 a)
```

