# lc-reasoner

Domain reasoner for the λ-calculus, implemented using the [Ideas](https://ideas.science.uu.nl/) library.

## Description of the reasoner

TODO

## Build instructions

The project has been tested with the following toolchain versions:

* GHC 9.2.8
* cabal-install 3.10.3.0

To build, run the following command:

```sh
cabal build
```

To run the project, giving it inputs from a local XML file, use:

```sh
cabal run . -- -f <FILE>
```

To run the project as a CGI script, first build it, then copy the resulting executable to your cgi-bin directory (locations depend on your Cabal version and HTTP server, see [build.sh](build.sh)).
