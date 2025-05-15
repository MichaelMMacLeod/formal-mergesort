{
  description = "Lean development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells.default = with pkgs;
          mkShell {
            nativeBuildInputs = [
              nixfmt-rfc-style
              elan
              (vscode-with-extensions.override {
                vscode = vscodium;
                vscodeExtensions = with vscode-extensions;
                  [
                    jnoortheen.nix-ide
                    timonwong.shellcheck
                    valentjn.vscode-ltex
                  ] ++ pkgs.vscode-utils.extensionsFromVscodeMarketplace [{
                    name = "lean4";
                    publisher = "leanprover";
                    version = "0.0.203";
                    sha256 =
                      "sha256-EA/m4l4TRnq002e6DZerXJhnOnyF628mqBjm+kiiElA=";
                  }];
              })
            ];
          };
      });
}
