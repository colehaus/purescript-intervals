let
  extras =
    import ./nix/extras.nix //
    import ./nix/gitignore.nix { inherit (pkgs) lib; };
  pkgs = extras.pinnedPkgs {
    specFile = ./nix/nixpkgs.json;
    opts = {};
  };
in
  extras.callPurescript2nix {
    inherit pkgs;
    name = "purescript-intervals";
    src = extras.gitignoreSource ./.;
    executable = false;
  }
