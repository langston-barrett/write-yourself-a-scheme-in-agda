{ pkgs ? import <nixpkgs> { } }:

# This commit has mkShell: https://github.com/NixOS/nixpkgs/pull/30975
import (pkgs.fetchFromGitHub {
  owner  = "NixOS";
  repo   = "nixpkgs";
  rev    = "45e47c14bee731f49c0110c4fa19a92833164031";
  sha256 = "1xkqmb6j0kay5m7nzv9rykx89q9i5b7xrbj9hkqmqwwcfyjv19r8";
}) { }
