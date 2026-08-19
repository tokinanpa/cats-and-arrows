{
  pkgs ? import <nixpkgs> { },
  idris2-pkgs ?
    (builtins.getFlake "github:mattpolzin/nix-idris2-packages")
    .packages.${pkgs.stdenv.hostPlatform.system},
  out ? pkgs.callPackage ./package.nix {
    inherit (idris2-pkgs) buildIdris';
  },
}:
let
  inherit (pkgs)
    mkShellNoCC
    ;
  inherit (idris2-pkgs)
    idris2
    ;
in
mkShellNoCC {
  inputsFrom = [ out.withSource ];

  packages = [
    idris2
  ];
}
