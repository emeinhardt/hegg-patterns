{
  description = "A Haskell package providing some hegg rewrite rules for common algebraic identities.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Change 945 appropriately to select a different GHC version
        haskellPackages = pkgs.haskell.packages.ghc945;

        jailbreakUnbreak = pkg:
          pkgs.haskell.lib.doJailbreak (pkg.overrideAttrs (_: { meta = { }; }));

        packageName = "hegg-patterns";
      in {
        packages.${packageName} =
          haskellPackages.callCabal2nix packageName self rec {
            # Dependency overrides go here
          };

        packages.default = self.packages.${system}.${packageName};
        defaultPackage = self.packages.${system}.default;

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [

            haskellPackages.haskell-language-server
            haskellPackages.hlint
            haskellPackages.stylish-haskell
            haskellPackages.hindent
            cabal-install

            # Optional: Only needed to make use of ./justfile
            just

            # Optional: Only needed to make use of ./dev/cabal-gen-docs.sh
            coreutils
          ];
          inputsFrom = map (__getAttr "env") (__attrValues self.packages.${system});
        };
        devShell = self.devShells.${system}.default;
      });
}
