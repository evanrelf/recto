let
  pkgs = import <nixpkgs> { };

  recto = pkgs.haskellPackages.callCabal2nix "recto" ./. { };

in
recto.env.overrideAttrs (prev: {
  buildInputs = [
    pkgs.cabal-install
    pkgs.ghcid
  ];
})
