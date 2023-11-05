{ mkDerivation, base, hegg, lib }:
mkDerivation {
  pname = "hegg-patterns";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base hegg ];
  description = "Rewrite rules for common algebraic identities, for use with [hegg](https://hackage.haskell.org/package/hegg).";
  license = lib.licenses.mit;
}
