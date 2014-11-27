#/bin/sh
ghc -rtsopts   -XStandaloneDeriving -O2 constants.hs forging.hs postructures.hs multibranch.hs
