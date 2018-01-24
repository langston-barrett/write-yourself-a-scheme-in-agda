{ pkgs ? import ./pinned-pkgs.nix { } }:

with pkgs; mkShell {
  shellHook = "exec zsh";
  mergeInputs = [ (callPackage ./default.nix { }) ];
}
