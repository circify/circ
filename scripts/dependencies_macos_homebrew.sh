set -xe

# breaks on M1 processors for now
# https://github.com/coin-or-tools/homebrew-coinor/issues/62
brew tap coin-or-tools/coinor
brew install coin-or-tools/coinor/cbc

brew tap cvc4/cvc4
brew install cvc4/cvc4/cvc4
