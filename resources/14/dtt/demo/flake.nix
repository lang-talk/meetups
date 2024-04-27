{
  description = "Agda demo";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
    lean.url = "github:leanprover/lean4?ref=v4.3.0";
  };

  outputs = { self, lean, nixpkgs }: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
    leanPkgs = lean.packages.${system};
    agda = pkgs.agda.withPackages (p: with p;[
      standard-library
    ]);
  in {
    devShells.${system}.default = pkgs.mkShell {
      name = "agda-demo";

      packages = [ agda pkgs.lean4 ];

      env.LEAN_MODE = "${leanPkgs.lean4-mode}/share/emacs/site-lisp/elpa/lean4-mode-1";
    };
  };
}
