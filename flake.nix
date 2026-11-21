{
  description = "Development tools for free-foil-lean";

  inputs = {
    backlog-md.url = "github:MrLesk/Backlog.md/v1.56.0";
    nixpkgs.follows = "backlog-md/nixpkgs";
  };

  outputs =
    { backlog-md, nixpkgs, ... }:
    let
      forBacklogSystems = f: builtins.mapAttrs f backlog-md.packages;
    in
    {
      packages = forBacklogSystems (
        _system: upstream: {
          backlog = upstream.backlog-md;
        }
      );

      devShells = forBacklogSystems (
        system: upstream:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell {
            packages = [
              upstream.backlog-md
              pkgs.lean4
            ];
          };
        }
      );
    };
}
