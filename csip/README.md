

Csip is a minimalistic Agda-like language for writing efficient programs
with high-level abstractions.

Compared to Agda, Csip can do staged compilation, it does not have termination checking
and it has a minimal but practical set of language features.

Warning: It is not advised to use Csip yet, it is under development.


## Installation

1.  Install the GHC Haskell compiler.
2.  Execute the following command:

        ./build


## Usage

The extension of Csip source files is `.csip`

The first lines of `.csip` files are directives which tell the compiler what to do.  
Main directives:

| Directive           | What will be printed |
| ---                 | ---         |
| `# source`          | source code |
| `# source quote`    | inner representation of the source code |
| `# indent quote`    | inner representation of the unindented source code |
| `# lex quote`       | token list |
| `# structure quote` | parse tree with whitespace |
| `# layout quote`    | parse tree |
| `# op quote`        | parse expression |
| `# exptree quote`   | parse expression with mixfix operators |
| `# sugar quote`     | desugared source code |
| `# scope`           | scope checked source code |
| `# elab`            | elaborated main expression |
| `# eval`            | normalized main expression |
| `# stage`           | staged main expression |
| `# haskell_stage`   | staged main expression parsable with Haskell Read instance |


### Compilation

Compilation of source files:

    csip FILE...

The output is written to the standard output.

Note that the compiler output is cached.


### Interactive mode

Interactive compilation of source files:

    csip show FILE...

Available commands in interactive mode:

| Keystroke | Description |
| ---       | ---         |
| `q`       | exit        |
| `r`       | reload      |
| Up, Down, PageUp, PageDown | scroll window |
| Left, Right | navigate between files |


## Documentation

You can read the documentation of Csip with

    csip show `find test/doc`

If needed, the documentation is readable without the interactive mode:

    csip export `find test/doc` >doc.txt
    less -R doc.txt


## Features

### Elaboration

The dependent typechecking algorithm is based on Coquand's algorithm,
as implemented in [András Kovács's elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).  
Differences:

- Csip uses globally unique names instead of De Bruijn indices.  
- Csip's value representation uses observable implicit sharing.  
  Implicit sharing of Haskell is made visible by adding unique identifiers
  (names) to each node of the value graph.
- The explicit/implicit distinction of lambdas and applications are erased in terms and values.
- Terms may contain closed values.
- Generated terms are marked.
- Forcing of flexible values is speeded up by caching the main blocking metavariable
  in flexible values.  
- Glued representation is implemented with an extra constructor for values.
- Algebraic data types are supported.

### Algebraic data types

- Data types and functions are open, which means
  that type constructors, data constructors and function alternatives
  can be given in any order obeying dependency.
- Type checking of functions alternatives happens separately for the left hand side
  and the right hand side. Eliminators are not used.
- Function alternatives are interpreted as rewrite rules.
- Rewrite rules are compiled to matching on individual constructors.
- The right hand sides of the rewrite rules are marked.
  Rewrite rule application is successful only if the right hand side is reached.
- Rewrite rules of the same function are chained together, i.e.
  if the left hand side of a rule does not match, the next rule of the same function is tried.

### Staging

Staged compilation is defined in [András Kovács's staged repository](https://github.com/AndrasKovacs/staged).

In csip, the representation of object code constructs is an ordinary HOAS in the meta language.
There are no splice and quote operations.
Object code function applications and lambdas are inserted by coercive subtyping.
The staging algoritm is open normalization plus transformation of object code
applications, lambdas and lets to raw applications, lambdas and lets.


## Development workflow

    runhaskell src/A_Meta.hs && ./build
    ./csip `find test`
    time ./csip diff `find test`
    <<< start_loop >>>
    <<< edit source files >>>
    runhaskell src/A_Meta.hs && ./build && time ./csip diff `find test`
    <<< goto start_loop >>>


## Examples

```haskell
\a b -> ((a + b)^100 + b)^80
```

is compiled to

```haskell
\z b -> (do
      n = Add z b
      n1 = Mul n (Mul n n)
      n2 = Mul n1 n1
      n3 = Mul n2 n2
      n4 = Mul n (Mul n3 n3)
      n5 = Mul n4 n4
      n6 = Add (Mul n5 n5) b
      n7 = Mul n6 n6
      n8 = Mul n6 (Mul n7 n7)
      n9 = Mul n8 n8
      n10 = Mul n9 n9
      n11 = Mul n10 n10
      Mul n11 n11
    )
```

given the definitions in [`test/staging/powerFast.csip`](test/staging/powerFast.csip)

and compiled to

```haskell
do
  sqr = \a -> Mul a a
  \z b -> (do
          n = Add z b
          n1 = Add (sqr (sqr (Mul n (sqr (sqr (sqr
                        (Mul n (sqr n))
                        )))))) b
          sqr (sqr (sqr (sqr (Mul n1
                    (sqr (sqr n1))
                    )))))
```

given the definitions in [`test/staging/powerFast2.csip`](test/staging/powerFast2.csip).

