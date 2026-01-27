{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";

    packageset.url = "github:mattpolzin/nix-idris2-packages";
    # don't set any follows for packageset if you want to benefit
    # from the Cachix cache. otherwise, go ahead.
  };

  outputs =
    {
      self,
      nixpkgs,
      packageset,
      ...
    }:
    let
      lib = nixpkgs.lib;
      forEachSystem =
        f:
        lib.genAttrs lib.systems.flakeExposed (
          system:
          f {
            inherit system;
            inherit (packageset.packages.${system}) idris2 idris2Lsp buildIdris' idris2Packages;
            pkgs = nixpkgs.legacyPackages.${system};
          }
        );
    in
    {
      packages = forEachSystem (
        { buildIdris', ... }:
        {
          default = buildIdris' {
            ipkgName = "type-test";
            src = ./.;
            extraIdrisLibraries = [
              # idris2Packages.packdb.ncurses-idris
            ];
          };
        }
      );

      devShells = forEachSystem (
        {
          system,
          pkgs,
          idris2,
          idris2Lsp,
          ...
        }:
        {
          default = pkgs.mkShell {
            packages = [
              idris2
              idris2Lsp
            ];
            inputsFrom = [ self.packages.${system}.default.withSource ];
          };
        }
      );
    };

  nixConfig = {
    extra-substituters = [
      "https://gh-nix-idris2-packages.cachix.org"
    ];
  };
}
