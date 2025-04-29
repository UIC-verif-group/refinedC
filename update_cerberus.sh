#!/bin/bash

# Usage: just enter the new hash bellow, and run the script from the root of
# the repository. Note that the script is self-modifying: it will change the
# old hash into the new one, and erase the new hash again.

OLD_HASH=6e3e8be7a3f75b1f1cb0704dca8ef3945be0e413
NEW_HASH=

sed -i "s/${OLD_HASH}/${NEW_HASH}/g" README.md DEVELOPERS.md .gitlab-ci.yml update_cerberus.sh Makefile
sed -i "s/^NEW_HASH=.*/NEW_HASH=/g" update_cerberus.sh
