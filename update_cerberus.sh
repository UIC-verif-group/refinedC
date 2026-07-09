#!/bin/bash

# Usage: just enter the new hash bellow, and run the script from the root of
# the repository. Note that the script is self-modifying: it will change the
# old hash into the new one, and erase the new hash again.

OLD_HASH=f11e6b335a687c1b77539f7e5695607d09dfc3ea
NEW_HASH=

sed -i "s/${OLD_HASH}/${NEW_HASH}/g" README.md DEVELOPERS.md .gitlab-ci.yml update_cerberus.sh Makefile
sed -i "s/^NEW_HASH=.*/NEW_HASH=/g" update_cerberus.sh
