{
  stdenv,
  lib,
  buildIdris' ?
    (builtins.getFlake "github:mattpolzin/nix-idris2-packages")
    .packages.${stdenv.hostPlatform.system}.buildIdris',
}:

buildIdris' {
  ipkgName = "cats-and-arrows";
  src = ./.;

  meta = {
    description = "A categorical foundation for a new effect system, written in Idris2";
    license = lib.licenses.mit;
  };
}
