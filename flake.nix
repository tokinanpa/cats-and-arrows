{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    systems.url = "github:nix-systems/default";
    idris2-packages.url = "github:mattpolzin/nix-idris2-packages";
  };

  nixConfig = {
    extra-substituters = [
      "https://gh-nix-idris2-packages.cachix.org"
    ];
    extra-trusted-public-keys = [
      "gh-nix-idris2-packages.cachix.org-1:iOqSB5DrESFT+3A1iNzErgB68IDG8BrHLbLkhztOXfo="
    ];
  };

  outputs =
    {
      self,
      nixpkgs,
      systems,
      idris2-packages,
      ...
    }:
    let
      eachSystem = func: nixpkgs.lib.genAttrs (import systems) (system: func (systemLocal system));

      # System-local values
      systemLocal = system: rec {
        inherit system;
        pkgs = nixpkgs.legacyPackages.${system};
        idris2-pkgs = idris2-packages.packages.${system};

        out = pkgs.callPackage ./package.nix {
          inherit (idris2-pkgs) buildIdris';
        };
      };
    in
    {
      packages = eachSystem (
        { out, ... }:
        {
          ${out.pname or out.name} = out;
          default = out;
        }
      );

      devShells = eachSystem (
        {
          pkgs,
          idris2-pkgs,
          out,
          ...
        }:
        {
          default = import ./shell.nix {
            inherit pkgs idris2-pkgs out;
          };
        }
      );
    };
}
