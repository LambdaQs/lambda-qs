# Formalization of the Lambda-Q# calculus

## Requirements
Working installation of Coq and Haskell.

- We recommend installing a recent version of [Coq Platform](https://github.com/coq/platform#usage-of-the-2021021-release), then
  issue `opam install dune ott` to get `dune` and `ott` installed.

We need a modified version of `lngen` in the `vendor` directory. Either clone this repo recursively:

```
git clone --recurse-submodules https://github.com/k4rtik/lambda-qs.git
```
or if already cloned, use:

```
git submodule update --init --recursive
```
to obtain the submodule. Then `lngen` needs to be built like so:

```
cd vendor/lngen
cabal build
cd -
```
See its README for any requirements.

## Build
`dune build` for build and `dune clean` for cleanup.

## Hacking
Use VSCode with VSCoq extension or any other Proof General-based IDE for Coq. Once built, things should work.

Use the `vendor` directory for external libraries.

## Misc
[Stlc](Stlc/README.md) contains an STLC Tutorial using Locally Nameless representation by Stephanie Weirich that we are using as a reference for this work.
