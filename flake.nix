{
  description = "A core language for rule-based hardware design";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/release-25.05";
  };

  outputs = { self, flake-utils, nixpkgs, ... }:
    let koikaPkg = { pkgs, lib, mkCoqDerivation, coq, boost, doCheck ? false, }:
      mkCoqDerivation rec {
        pname = "koika";
        defaultVersion = "0.0.1";

        # derivation is build using "dune build -p {opam-name}"
        opam-name = "koika";
        useDune = true;

        release."0.0.1" = {
          src = lib.cleanSourceWith {
            src = lib.cleanSource ./.;
            filter = let inherit (lib) all hasSuffix; in
              path: _: all (x: !hasSuffix x path) [
                "flake.nix"
                ".gitignore"
              ];
            };
        };

        enableParallelBuilding = true;

        # run-time dependencies
        buildInputs = [
          boost
        ];

        nativeBuildInputs = with pkgs; [
          gnumake git bash
        ];

        # Coq/ocaml libraries and Coq plugins (necessary to propagate PATH)
        propagatedBuildInputs = with coq.ocamlPackages; [
          findlib
          base
          core
          core_unix
          stdio
          parsexp
          hashcons
          zarith
        ];

        configurePhase = ''
          make configure
        '';

        inherit doCheck;
        checkPhase = ''
          runHook preCheck
          make all
          runHook postCheck
        '';
      }; in
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs {
        inherit system;
        overlays = [ self.overlays.default ];
      }; in rec {
        checks = {
          koika = packages.default.override { doCheck = true; };
        };

        devShells.default = packages.default;

        packages = rec {
          default = coq8_18-koika;
          coq8_18-koika = pkgs.coqPackages_8_18.koika;
        };
      }
    )
    // {
      # NOTE: To use this flake, apply the following overlay to nixpkgs and use
      # koika from its respective coqPackages_VER attribute set!
      overlays.default = final: prev:
        prev.lib.mapAttrs (name: _:
          prev.${name}.overrideScope (
            self: _: { koika = self.callPackage koikaPkg { }; }
          )
        ) {
          inherit (final) coqPackages_8_18;
        };
    };
}
