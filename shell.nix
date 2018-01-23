{ pkgs ? import ./pinned-pkgs.nix { } }:

with pkgs; mkShell {
  shellHook = "exec zsh";

  buildInputs = [
    haskellPackages.Agda
    # to compile agda files, we need a few more haskell packages
    (haskellPackages.ghcWithPackages (pkgs: with pkgs; [ieee text]))
  ];
}
