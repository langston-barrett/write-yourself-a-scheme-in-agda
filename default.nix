{ pkgs ? import ./pinned-pkgs.nix { } }:
# { stdenv, agda, fetchgit, AgdaStdlib }:

with pkgs; stdenv.mkDerivation rec {
  version = "0.1";
  name = "agda-scheme-${version}";

  src = ./.;

  buildInputs = [
    git
    haskellPackages.Agda
    # to compile agda files, we need a few more haskell packages
    (haskellPackages.ghcWithPackages (pkgs: with pkgs; [ieee text]))
  ];

  buildPhase = ''
    for project in "agda/agda-stdlib" "gallais/agdARGS" "gallais/agdarsec"; do
      git clone "https://github.com/$project" || true
    done
    # For some reason, there is an error that doesn't happen when called
    # manually: <stdout>: commitBuffer: invalid argument (invalid character)
    agda --library-file=./libraries \
         --library=standard-library \
         --library=agdarsec \
         --library=agdARGS \
         --compile-dir=build \
         -i "$PWD" \
         -c Main.agda
  '';

  meta = {
    homepage = https://github.com/siddharthist/write-yourself-a-scheme-agda;
    description = "";
    license = stdenv.lib.licenses.mpl2;
    platforms = stdenv.lib.platforms.unix;
    maintainers = with stdenv.lib.maintainers; [ siddharthist ];
  };
}
