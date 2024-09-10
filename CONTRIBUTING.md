# Contributing to Kôika

To start contributing, you need a GitHub account and create a pull-request against this repository.
See [here](https://docs.github.com/en/get-started/quickstart/hello-world) for a primer.

# How to do

## Before submitting a pull request

Run the tests to check if your changes broke anything.
If you are only using opam/dune (i.e. not nix), run:

```sh
make all
```

In case you are using nix, you can also run:

```sh
nix flake check
```

## Locally reproduce a CI run

Suppose you want to reproduce a CI run locally, maybe because it has failed on GitHub or because you want to run it on a different commit of a pull request that consist of multiple commits.

In case you have nix you can simply run these 2 commands (which should be identical with the [CI script](./.github/workflows/flake-build.yml))

```sh
nix build
nix flake check
```

Both commands can also be executed with a specific version of the repository using:

```sh
nix build 'github:mit-plv/koika?ref=96e4859...'
nix flake check 'github:mit-plv/koika?ref=96e4859...'
```

In case you don't have nix it is harder to reproduce the exact versions of all dependencies but once you have them you can reproduce the CI build using:

```sh
# equivalent to 'nix build'
make configure
dune build -p koika

# equivalent to 'nix flake check'
make all
```

