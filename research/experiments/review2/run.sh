#!/bin/sh
export BEND_NO_TELEMETRY=1
for f in "$@"; do
  printf '=== %s\n' "$f"
  ~/.bend/bin/bend "$f" --check-only 2>&1 | tail -12
done
