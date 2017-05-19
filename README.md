# A Haskell library to translate ABS programs to Haskell equivalent code

[![Build Status](https://travis-ci.org/abstools/habs.svg)](https://travis-ci.org/abstools/habs) [![License (3-Clause BSD)](https://img.shields.io/badge/license-BSD--3-blue.svg?style=flat)](http://opensource.org/licenses/BSD-3-Clause)
 ([Documentation](http://abstools.github.io/habs)) ([Test Results](http://abstools.github.io/habs/test-results.html))

A Haskell library to translate ABS programs to Haskell equivalent code.

# Prerequisites

Before installing the HABS backend, you need the Glasgow Haskell Compiler (**GHC**) version >= 8.

a) Getting GHC on Ubuntu-Linux >= 17.04

```bash
apt-get update
apt-get install ghc cabal-install happy zlib1g-dev
```

b) Getting GHC on *-Linux, Windows, Mac

Get the Haskell Platform for your OS from <https://www.haskell.org/platform>

# Installing the HABS backend

Clone and navigate to this repository:

```bash
git clone https://github.com/abstools/habs
cd habs/
```

Then, from inside the repository run:

```bash
git submodule update --init

cabal sandbox init
cabal sandbox add-source habs-parser
cabal sandbox add-source habs-stdlib
cabal sandbox add-source habs-runtime

cabal update
cabal install
```

# Updating & Re-installing the HABS backend

Navigate to the cloned repository directory and run:

```bash
cd habs/
git pull
git submodule update
cabal update
cabal install
```

# Compiling & Running an ABS program using the HABS backend

From inside the cloned repository run:

```bash
cd habs/
cabal exec habs -- Module1.abs Module2.abs

# the translated files are placed under gen/haskell
cabal exec ghc -- gen/haskell/*.hs --make -main-is Module1

# Run the main ABS program
./gen/haskell/Module1
```

  , where `-main-is` should point to the module which contains the main ABS block you want to execute.
  
# Contributing

The backend has been split into multiple subrepositories (git submodules):

- [habs-parser](https://github.com/abstools/habs-parser): Contains the grammar & parser to parse ABS files.
- [habs-runtime](https://github.com/abstools/habs-runtime): A library to implement the concurrency features of the ABS language inside Haskell.
- [habs-stdlib](https://github.com/abstools/habs-stdlib): The ABS standard library expressed in Haskell.
- [habs](https://github.com/abstools/habs) (This repository): Contains the code-generator of ABS to Haskell.
- [habs-samples](https://github.com/abstools/habs-samples): Contains an ABS test suite and other sample ABS files.
