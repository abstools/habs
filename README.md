# A Haskell library to translate ABS programs to Haskell equivalent code

[![Build Status](https://travis-ci.org/abstools/habs.svg)](https://travis-ci.org/abstools/habs) [![License (3-Clause BSD)](https://img.shields.io/badge/license-BSD--3-blue.svg?style=flat)](http://opensource.org/licenses/BSD-3-Clause)
 ([online API docs](http://abstools.github.io/habs)) ([testing results](http://abstools.github.io/habs/test-results.html))

A Haskell library to translate ABS programs to Haskell equivalent code.

# Prerequisites

Before installing the HABS backend, you need the Glasgow Haskell Compiler (**GHC**) version >= 7.10.

a) Getting GHC on Ubuntu-Linux >= 16.04

```
apt-get update
apt-get install ghc cabal-install happy zlib1g-dev
```

b) Getting GHC on *-Linux, Windows, Mac

Get the Haskell Platform for your OS from <https://www.haskell.org/platform>

# Installing the HABS backend

Clone and navigate to this repository:

```
git clone https://github.com/abstools/habs
cd habs/
```

Then, from inside the repository run:

```
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

```
cd habs/
git pull
git submodule update
cabal update
cabal install
```

# Compiling & Running an ABS program using the HABS backend

From inside the cloned repository run:

```
cd habs/
cabal exec habs -- Module1.abs Module2.abs

# the translated files are placed under gen/haskell
cabal exec ghc -- gen/haskell/*.hs --make -main-is Module1

# Run the main ABS program
./gen/haskell/Module1
```

  , where `-main-is` should point to the module which contains the main ABS block you want to execute.