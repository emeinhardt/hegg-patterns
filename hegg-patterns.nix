{ mkDerivation, base, hegg, lib }:
mkDerivation {
  pname = "hegg-patterns";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base hegg ];
  homepage = "https://github.com/emeinhardt/hegg-patterns";
  description = "E-graph rewrite rules for common algebraic identities, for use with hegg";
  license = lib.licenses.mit;
}
