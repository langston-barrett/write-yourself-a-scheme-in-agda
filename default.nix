{ pkgs ? import ./pinned-pkgs.nix { } }:
# { stdenv, agda, fetchgit, AgdaStdlib }:

with pkgs; stdenv.mkDerivation rec {
  version = "0.1";
  name = "agda-scheme-${version}";

  src = lib.sourceFilesBySuffices ./. [ ".agda" ".lagda" ".agda-lib" "libraries" ];

  buildInputs = [
    git
    glibcLocales
    haskellPackages.Agda
    # to compile agda files, we need a few more haskell packages
    (haskellPackages.ghcWithPackages (pkgs: with pkgs; [ieee text]))
  ];

  # What to run when people run nix-shell
  # shellHook = ''
  #   export PROMPT="[nix shell] $PROMPT"
  # '';

  buildPhase = ''
    # Travis error: https://api.travis-ci.org/v3/job/333153489/log.txt
    if [[ -n "$TRAVIS" ]]; then
      git config --global http.sslVerify false
    fi

    for project in "agda/agda-stdlib" "gallais/agdARGS" "gallais/agdarsec"; do
      git clone "https://github.com/$project" || true
    done

    # See https://github.com/agda/agda/issues/2922
    export LANG=en_US.UTF-8
    export LC_CTYPE=en_US.UTF-8
    export LC_ALL=en_US.UTF-8

    agda --library-file=./libraries \
         --library=standard-library \
         --library=agdarsec \
         --library=agdARGS \
         --compile-dir=build \
         -i "$PWD" \
         -c Main.agda
  '';

  installPhase = ''
    mkdir -p $out/bin
    cp build/Main $out/bin/agda-scheme
  '';

  meta = {
    homepage = https://github.com/siddharthist/write-yourself-a-scheme-agda;
    description = "Like 'Write Yourself a Scheme in 48 Hours, but in Agda!";
    license = stdenv.lib.licenses.mpl20;
    platforms = stdenv.lib.platforms.unix;
    maintainers = with stdenv.lib.maintainers; [ siddharthist ];
  };
}
