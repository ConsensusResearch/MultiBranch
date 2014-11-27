#/bin/sh
ghc -rtsopts -threaded -O2 -static -optl-pthread -optl-static -XStandaloneDeriving -O2 constants.hs forging.hs postructures.hs multibranch.hs
