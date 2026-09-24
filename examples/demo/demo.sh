#!/usr/bin/env bash
# Scripted terminal session for the launch clip: each command is typed, then really run.
# Record: asciinema rec --window-size 196x34 -c examples/demo/demo.sh demo.cast
cd "$(dirname "$0")" || exit 1
export BEND_NO_TELEMETRY=1 PATH="$HOME/.bend/bin:$PATH"

type_out() { printf '\033[1;32m$\033[0m '; for ((i = 0; i < ${#1}; i++)); do printf '%s' "${1:i:1}"; sleep 0.025; done; printf '\n'; }
say() { printf '\033[2;37m%s\033[0m\n' "$1"; sleep 1.2; }
run() { type_out "$1"; sleep 0.3; eval "$1"; sleep "${2:-1.5}"; }

clear
say "# Bend 2. Goal: prove  length(reverse(xs ++ ys)) == length(ys ++ xs)"
say "# By hand you first need lemmas about +, length and reverse:"
run "wc -l before.bend && bend before.bend --check-only" 2
say "# With bend-mathlib: two imports and a four-step proof:"
run "cat after.bend" 6
run "bend after.bend --check-only" 2.5
say "# import bend-mathlib@0.1.0.0  ·  github.com/bendlib/bendlib"
sleep 2
