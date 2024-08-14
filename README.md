<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Dice Partitions

[![Docker CI][docker-action-shield]][docker-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/motrellin/dice-partitions/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/motrellin/dice-partitions/actions/workflows/docker-action.yml

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://motrellin.github.io/dice-partitions/./docs/toc.html

A program to find all possibilities, how to roll w dices to get a total sum of s.

## Meta

- Author(s):
  + Max Ole Elliger (initial)
- License: [BSD 3-Clause "New" or "Revised" License](LICENSE)
- Compatible Coq versions: Developed for 8.19
- Additional dependencies:
  + Coq Equations
- Coq namespace: `DicePart`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Dice Partitions
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-dice-partitions
```

To instead build and install manually, do:

``` shell
git clone --recurse-submodules https://github.com/motrellin/dice-partitions.git
cd dice-partitions
make all  # or make -j <number-of-cores-on-your-machine> all
make install
```
