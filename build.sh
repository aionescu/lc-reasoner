#!/usr/bin/env bash
set -euo pipefail

# Note: This is just a quick script to build and copy the CGI executable to the right directory on my machine.
# It's not meant to be reproducible, or to work on other machines.

cabal build
cp \
  dist-newstyle/build/x86_64-linux/ghc-9.2.8/lc-reasoner-0.0.0.0/x/lc-reasoner/build/lc-reasoner/lc-reasoner \
  /srv/http/cgi-bin/lc-reasoner.cgi
