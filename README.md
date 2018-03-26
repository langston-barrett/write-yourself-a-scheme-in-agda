# Write Yourself a Scheme in Agda

This is very much a work in progress. I'm trying to
learn [Agda](https://en.wikipedia.org/wiki/Agda_(programming_language)), and it
seems that there aren't enough longer tutorials. 

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-generate-toc again -->
**Table of Contents**

- [Write Yourself a Scheme in Agda](#write-yourself-a-scheme-in-agda)
    - [Progress](#progress)
    - [Installation](#installation)
        - [Nix](#nix)
        - [Building](#building)

<!-- markdown-toc end -->


## Progress

The following lists the parts of ["Write Yourself A Scheme"] and whether or not
they're implemented:

 - [x] First Steps: Compiling and running
 - [x] Parsing
 - [x] Evaluation, Part 1
 - [x] Error Checking and Exceptions
 - [ ] Evaluation, Part 2
 - [ ] Building a REPL: Basic I/O
 - [ ] Adding Variables and Assignment: Mutable State in Haskell
 - [ ] Defining Scheme Functions: Closures and Environments
 - [ ] Creating IO Primitives: File I/O
 - [ ] Towards a Standard Library: Fold and Unfold
 - [ ] Conclusion & Further Resources
 
<!--
## Features

This Scheme doesn't come nearly as close to the one in that Wikibook
to being [R5RS](http://www.schemers.org/Documents/Standards/R5RS/HTML/)-compliant.
This flexibility allows for some interesting features:

 1. Variadic primitives: There are combinators for constructing primitive
    functions. One such combinator takes binary functions on `Lisp`
    values to variadic ones via a left fold; almost all primitive functions
    are implemented using it.

    * Heterogeneous equality: No need for `string=?`, all primitives can be
      tested for equality using just `=`:
        ```
        ./result/bin/agda-scheme "(= (+ 2 2) (+ 1 3) 4)"
        true
        ```

    * Transitive relations: 
        ```
        ./result/bin/agda-scheme "(≤ 2 3 4 5 6)"
        true
        ```
-->

## Installation

### Nix

If you use the [Nix](https://nixos.org/nix/) package manager, you can use
`nix-shell` to jump into a shell with 

 * Agda
 * GHC + two packages required for compiling Agda to binary

Building with `nix-build` doesn't currently work. 

### Building

Do this:
```bash
for project in "agda/agda-stdlib" "gallais/agdARGS" "gallais/agdarsec"; do
  git clone "https://github.com/$project" || true
done

agda --library-file=./libraries \
      --library=standard-library \
      --library=agdarsec \
      --library=agdARGS \
      --compile-dir=build \
      -i "$PWD" \
      -c Main.agda
```

This clones the following three libraries:

 * https://github.com/agda/agda-stdlib
 * https://github.com/gallais/agdARGS
 * https://github.com/gallais/agdarsec
 
and then compiles the main file.

[wyas]: https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours
