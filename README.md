# Write Yourself a Scheme in Agda

This is very much a work in progress. I'm trying to
learn [Agda](https://en.wikipedia.org/wiki/Agda_(programming_language)), and it
seems that there aren't enough longer tutorials. I hope to someday document this
excursion enough to make it worthy of its title.

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
