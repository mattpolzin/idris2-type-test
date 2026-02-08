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
            inherit (packageset.packages.${system}) idris2 idris2Lsp buildIdris idris2Packages;
            pkgs = nixpkgs.legacyPackages.${system};
          }
        );
    in
    {
      packages = forEachSystem (
        { buildIdris, idris2, pkgs, idris2Packages, system, ... }:
          let postInstall =
              let
                name = "${idris2.pname}-${idris2.version}";
                idris2Support = idris2.passthru.idris2Support;
                globalLibraries = [
                  "\\$HOME/.nix-profile/lib/${name}"
                  "/run/current-system/sw/lib/${name}"
                  "${idris2}/${name}"
                ];
                globalLibrariesPath = builtins.concatStringsSep ":" globalLibraries;
                supportLibrariesPath = lib.makeLibraryPath [ idris2Support ];
                supportSharePath = lib.makeSearchPath "share" [ idris2Support ];
              in
              ''
                wrapProgram "$out/bin/type-test" \
                  --set-default CHEZ "${lib.getExe pkgs.chez}" \
                  --run 'export IDRIS2_PREFIX=''${IDRIS2_PREFIX-"$HOME/.idris2"}' \
                  --suffix IDRIS2_LIBS ':' "${supportLibrariesPath}" \
                  --suffix IDRIS2_DATA ':' "${supportSharePath}" \
                  --suffix IDRIS2_PACKAGE_PATH ':' "${globalLibrariesPath}" \
                  --suffix LD_LIBRARY_PATH ':' "${supportLibrariesPath}" \
                  --suffix DYLD_LIBRARY_PATH ':' "${supportLibrariesPath}" \
              '';
            pkg = buildIdris {
            ipkgName = "type-test";
            src = ./.;
            idrisLibraries = [
              idris2Packages.packdb.hedgehog
              idris2Packages.idris2Api
            ];
          };
          in
        {
          type-test = pkg.executable.overrideAttrs { inherit postInstall; };
          type-testApi =  pkg.library';
          default =  self.packages.${system}.type-test;
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
