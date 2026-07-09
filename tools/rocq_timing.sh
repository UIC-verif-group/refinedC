#!/bin/bash

set -e

# Wrapper for rocq that is used when running the perf script in CI.
# Variable TIMECMD is expected to contain an absolute path to the perf script.
# If TIMECMD is not set (or empty), fallback to just calling rocq.
#
# We need to use "opam exec -- rocq" to get the rocq installed by opam, and not
# just invoke this script recursively.
#
# If PROFILE is set, generate a profile in the $PROFILE file (relative to the
# root of the repo).

# This file is in "_build/default/tools"
REPO_DIR="$(dirname $(readlink -f $0))/../../../"

PROFILE_ARG=()
if [[ ! -z "$PROFILE" ]]; then
    PROFILE_ARG=("-profile" "$REPO_DIR/$PROFILE")
fi

COMMAND="$1"
shift

if [[ "$COMMAND" = "c" || "$COMMAND" = "compile" ]]; then
  opam exec -- ${TIMECMD} rocq "$COMMAND" "${PROFILE_ARG[@]}" "$@"
else
  opam exec -- rocq "$COMMAND" "$@"
fi
