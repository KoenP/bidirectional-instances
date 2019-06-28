{ mkDerivation, base, mtl, parsec, pretty, stdenv }:
mkDerivation {
  pname = "prototype";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [ base mtl parsec pretty ];
  license = stdenv.lib.licenses.bsd3;
}
