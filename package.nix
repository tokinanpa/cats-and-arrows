{
  stdenv,
  lib,
  buildIdris' ?
    (builtins.getFlake "github:mattpolzin/nix-idris2-packages")
    .packages.${stdenv.hostPlatform.system}.buildIdris',
}:

buildIdris' {
  ipkgName = "cats";
  src = ./.;

  meta = {
    description = "A generalized category/arrow hierarchy for Idris2";
    license = lib.licenses.mit;
  };
}
