{ pkgs ? import <nixpkgs> { } }:

import (pkgs.fetchFromGitHub {
  owner    = "NixOS";
  repo     = "nixpkgs";
  rev      = "18.03";
  sha256   = "0hk4y2vkgm1qadpsm4b0q1vxq889jhxzjx3ragybrlwwg54mzp4f";
}) { }
