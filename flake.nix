{
    description = "Continuous normalization";

    inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    outputs = { self, nixpkgs }:
      let
        system = "x86_64-linux";
        pkgs = nixpkgs.legacyPackages.${system};
        agda = pkgs.agda.withPackages (p: [ p.standard-library ]);
      in {
        devShells.${system}.default = pkgs.mkShell {
          buildInputs = [ agda ];
        };
      };
}
