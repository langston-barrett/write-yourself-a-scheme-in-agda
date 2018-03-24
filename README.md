# Write Yourself a Scheme in Agda

This is very much a work in progress. I'm trying to
learn [Agda](https://en.wikipedia.org/wiki/Agda_(programming_language)), and it
seems that there aren't enough longer tutorials. I hope to someday document this
excursion enough to make it worthy of its title.

<!--
Note that this Scheme doesn't come nearly as close to the one in that Wikibook
to being [R5RS](http://www.schemers.org/Documents/Standards/R5RS/HTML/)-compliant,
I am more concerned about getting a somewhat working interpreter out the door
than the accuracy of the "Scheme" it interprets.
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

## Progress

The following lists the parts of ["Write Yourself A Scheme"] and whether or not
they're implemented:

 - [x] First Steps: Compiling and running
 - [x] Parsing
 - [x] Evaluation, Part 1
 - [ ] Error Checking and Exceptions
 - [ ] Evaluation, Part 2
 - [ ] Building a REPL: Basic I/O
 - [ ] Adding Variables and Assignment: Mutable State in Haskell
 - [ ] Defining Scheme Functions: Closures and Environments
 - [ ] Creating IO Primitives: File I/O
 - [ ] Towards a Standard Library: Fold and Unfold
 - [ ] Conclusion & Further Resources

[wyas]: https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours
