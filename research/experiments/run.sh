#!/usr/bin/env bash
# research/experiments/run.sh — nightly regression for the F1–F34 grounded facts (PLAN.md §1).
#
# Each assertion replays one experiment and compares its OBSERVED outcome — exit code,
# exact verdict line, or checker error label — with the outcome PLAN.md §1 records.
# Facts with no such definable outcome are listed as explicit non-goals at the bottom;
# this is deliberately not a bare `--check-only` smoke runner.
#
# Usage:  bash research/experiments/run.sh              run all assertions (0 iff all pass)
#         bash research/experiments/run.sh --self-test   prove the harness can fail: plant a
#                                                       perturbed file and wrong expectations
# Env:    BEND_BIN (default $HOME/.bend/bin/bend), JOBS (lawcheck --jobs, default 4),
#         EXP_ROOT (default: this directory; used by --self-test).
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
BEND_BIN="${BEND_BIN:-$HOME/.bend/bin/bend}"
JOBS="${JOBS:-4}"
EXP_ROOT="${EXP_ROOT:-$SCRIPT_DIR}"
export BEND_NO_TELEMETRY=1

PASS=0
FAIL=0
pass() { PASS=$((PASS + 1)); printf '  ok    %s\n' "$1"; }
fail() { FAIL=$((FAIL + 1)); printf '  FAIL  %s\n' "$1"; }

resolve() { if [ -e "$EXP_ROOT/$1" ]; then printf '%s' "$EXP_ROOT/$1"; else printf '%s/%s' "$ROOT" "$1"; fi; }

BEND_EC=0
BEND_OUT=""
run_bend() { BEND_OUT="$("$BEND_BIN" "$1" --check-only 2>&1)"; BEND_EC=$?; }

# assert_bend <name> <file> <expected-exit> [required-substring]
assert_bend() {
  local name=$1 file=$2 want=$3 sub=${4:-}
  run_bend "$(resolve "$file")"
  if [ "$BEND_EC" -ne "$want" ]; then
    fail "$name (exit $BEND_EC, want $want): $(printf '%s' "$BEND_OUT" | tr '\n' ' ' | cut -c1-140)"
    return 1
  fi
  if [ -n "$sub" ] && ! printf '%s' "$BEND_OUT" | grep -qF -- "$sub"; then
    fail "$name (missing \"$sub\")"
    return 1
  fi
  pass "$name"
  return 0
}

# assert_lc <name> <file> <max-instances> [required-substring ...]  (lawcheck must exit 0)
assert_lc() {
  local name=$1 file=$2 inst=$3
  shift 3
  local out sub lc
  out="$(cd "$ROOT" && bun tools/lawcheck/cli.ts "$(resolve "$file")" --max-instances "$inst" --jobs "$JOBS" 2>&1)"
  lc=$?
  if [ "$lc" -ne 0 ]; then
    fail "$name (lawcheck non-zero): $(printf '%s' "$out" | tail -1 | cut -c1-140)"
    return 1
  fi
  for sub in "$@"; do
    if ! printf '%s' "$out" | grep -qF -- "$sub"; then
      fail "$name (missing \"$sub\")"
      return 1
    fi
  done
  pass "$name"
  return 0
}

suite() {
  printf '# F-fact regression on %s (bend %s)\n' "$BEND_BIN" "$("$BEND_BIN" version 2>/dev/null | awk '{print $2}')"

  # F4 — def unifies across versions iff its body is a plain Base application; matched
  # defs and datatypes are nominal at variable arguments; closed instances still unify.
  assert_bend "F4  t4a  Base-only le unifies at variables"            review2/t4a_user_le_var.bend 0 "All terms check."
  assert_bend "F4  t4d  closed allz instance normalizes and unifies"  review2/t4d_user_allz_closed.bend 0 "All terms check."
  assert_bend "F4  t4g  add2 (Base body) unifies at variables"        review2/t4g_user_add2_var.bend 0 "All terms check."
  assert_bend "F4  t4b  matched allz is nominal at variables"         review2/t4b_user_allz_var.bend 1 "Location: u2"
  assert_bend "F4  t4e  function-typed perm is nominal"               review2/t4e_user_perm_var.bend 1 "Location: u"
  assert_bend "F4  t4f  matched isz is nominal"                       review2/t4f_user_isz_var.bend 1 "Location: u"
  assert_bend "F4  user_adt datatype is nominal"                      user_adt.bend 1 "Location: use_tree"
  assert_bend "F4  t13a Base-only mem unifies"                        review2/t13a_mem_only.bend 0 "All terms check."
  assert_bend "F4  t13b Base-only sorted_b (List.all) unifies"        review2/t13b_user.bend 0 "All terms check."
  # F4b — two lemma packages sharing one predicate file interoperate.
  assert_bend "F4b t11  shared-kernel predicate interoperates"        review2/t11_user_kernel.bend 0 "All terms check."
  # F3 — namespace = file path; two versions are unrelated, closed instances still resolve.
  assert_bend "F3  v1/order.bend checks standalone"                   v1/order.bend 0 "All terms check."
  assert_bend "F3  v2/order.bend checks standalone"                   v2/order.bend 0 "All terms check."
  assert_bend "F3  core.bend (v1 consumer) checks"                    core.bend 0 "All terms check."
  assert_bend "F3  user_def.bend (v2 consumer, closed instance)"      user_def.bend 0 "All terms check."

  # F5 — a name spelled like a Base one is a hard error.
  assert_bend "F5  clash.bend duplicate Base law name"                lib/clash.bend 1 "duplicate declaration: Nat.ge_refl"
  assert_bend "F5  ctor.bend duplicate Base constructor"              ctor.bend 1 "duplicate declaration: Some"
  # F7 — user-module constructors are per-file namespaced (a.node, b.node coexist).
  assert_bend "F7  pa/a.bend and pb/b.bend same ctor name coexist"    pa/a.bend 0 "All terms check."
  assert_bend "F7  pb/b.bend same ctor name coexists"                 pb/b.bend 0 "All terms check."
  assert_bend "F7  both.bend two same-named types coexist"            both.bend 0 "All terms check."
  assert_bend "F7  t10_same_name two imports coexist"                 review2/t10_same_name.bend 0 "All terms check."

  # F8 — imported modules are fully re-checked on every check.
  assert_bend "F8  bad10.bend broken law is caught"                   bad10.bend 1 "Location: s5"
  assert_bend "F8  usebad.bend re-checks its import"                  usebad.bend 1 "Location: bad10.s5"
  # F10 — a LAWS/PROOF split forces importers to import both.
  assert_bend "F10 use_laws_only.bend fails (proof missing)"          use_laws_only.bend 1 "Location: t"
  assert_bend "F10 use_both.bend imports both and checks"             use_both.bend 0 "All terms check."
  # F11, F12, F13 — generics, templates, abstract ~-hypotheses.
  assert_bend "F11 glist.bend generics at &1 and &2"                  glist.bend 0 "All terms check."
  assert_bend "F12 tmpl2.bend templates check without unsafe"         tmpl2.bend 0 "All terms check."
  assert_bend "F13 lib/algebra.bend abstract ~-hypotheses"            lib/algebra.bend 0 "All terms check."
  assert_bend "F13 use_alg.bend instantiates the abstract layer"      use_alg.bend 0 "All terms check."
  # F16 — alias for our module works; Base spellings win.
  assert_bend "F16 alias_nat.bend alias checks"                       alias_nat.bend 0 "All terms check."

  # F25 — predicate returning Type cannot be a reusable + hypothesis; Data can.
  assert_bend "F25 t2c  +hyp of Type rejected"                        review2/t2c_plus_hyp_type.bend 1 "Location: use_twice"
  assert_bend "F25 t2d  +hyp of Data accepted"                        review2/t2d_plus_hyp_data.bend 0 "All terms check."
  assert_bend "F25 t2f  plain equality hyp not reusable"              review2/t2f_plain_eq_twice.bend 1 "Location: use_twice_eq"
  assert_bend "F25 t8   Data predicate is total/reusable"             review2/t8_le_data_total.bend 0 "All terms check."
  # F26 — statement-only binder must be erased; matched binder cannot be.
  assert_bend "F26 t1a  erased statement binder checks"               review2/t1a_erased.bend 0 "All terms check."
  assert_bend "F26 t1b  non-erased binder loses affinity"             review2/t1b_nonerased.bend 1 "Location: use_nonerased"
  assert_bend "F26 t1c  erased binder that is matched is rejected"    review2/t1c_erased_matched.bend 1 "Location: add_zero_r"
  # F27 — count-based perm hypothesis is single-use, even erased.
  assert_bend "F27 t5a  perm hypothesis used once checks"             review2/t5a_perm.bend 0 "All terms check."
  assert_bend "F27 t5b  perm reused (affine) is rejected"             review2/t5b_perm_reuse_affine.bend 1 "Location: twice"
  assert_bend "F27 t5c  perm reused (erased) is rejected"             review2/t5c_perm_reuse_erased.bend 1 "Location: twice"
  # F28 — composed template and Equal.sym twins check.
  assert_bend "F28 t3   map_map composed template checks"             review2/t3_map_map.bend 0 "All terms check."
  assert_bend "F28 t6   twins with Equal.sym check"                   review2/t6_twins.bend 0 "All terms check."
  # F29 — the typed `(a <= b : Nat)` form is the one that checks.
  assert_bend "F29 t2a  typed comparison form checks"                 review2/t2a_le_bool.bend 0 "All terms check."

  # F22 — a false closed law fails with expected/observed and its location.
  assert_bend "F22 inst.bend false {==} fails with expected/observed" lawcheck/inst.bend 1 "Location: c6"
  assert_bend "F22 inst.bend prints the expected/observed pair"       lawcheck/inst.bend 1 "expected :"

  # F21 — BEND_LIB names/<name>@<ver> -> hash -> working copy resolves imports locally.
  local tmplib; tmplib="$(mktemp -d)"
  mkdir -p "$tmplib/names"
  cp "$SCRIPT_DIR/devmode/devlib/names/bend-mathlib@0.2.0.0" "$tmplib/names/"
  ln -s "$SCRIPT_DIR/devmode/mono/bend-mathlib" "$tmplib/0x00000000000000000000000000000de1"
  BEND_OUT="$(BEND_LIB="$tmplib" "$BEND_BIN" "$SCRIPT_DIR/review2/t12_devmode.bend" --check-only 2>&1)"; BEND_EC=$?
  if [ "$BEND_EC" -eq 0 ] && printf '%s' "$BEND_OUT" | grep -qF "All terms check."; then
    pass "F21 t12_devmode.bend dev import by name@version resolves"
  else
    fail "F21 t12_devmode.bend (exit $BEND_EC)"
  fi
  BEND_OUT="$(BEND_LIB="$tmplib" "$BEND_BIN" "$SCRIPT_DIR/devmode/mono/bendlib-core/q.bend" --check-only 2>&1)"; BEND_EC=$?
  if [ "$BEND_EC" -eq 0 ] && printf '%s' "$BEND_OUT" | grep -qF "All terms check."; then
    pass "F21 q.bend dev consumer checks under BEND_LIB"
  else
    fail "F21 q.bend (exit $BEND_EC)"
  fi

  # F24 — the installed binary ships base.bend + effects, not bend.ts.
  if [ -f "$HOME/.bend/bend2/base.bend" ] && [ ! -e "$HOME/.bend/bend2/bend.ts" ]; then
    pass "F24 installed ~/.bend/bend2 has base.bend and no bend.ts"
  else
    fail "F24 installed ~/.bend/bend2 layout unexpected"
  fi

  # F31 — overflowing Nat.pow instances are dropped by name, not turned into `!`.
  assert_lc "F31 candidates nat.bend 0 failures, 0 errors" research/candidates/mathlib-0.2/nat.bend 100 \
    "46 laws: 46 ✓ · 0 ✗ · 0 ~ · 0 !"
  # F34 — the 0.2 candidate statements: 87 laws, 0 counterexamples, 0 checker errors, 1 skipped.
  assert_lc "F34 candidates bool.bend"           research/candidates/mathlib-0.2/bool.bend 100 "15 laws: 14 ✓ · 0 ✗ · 1 ~ · 0 !"
  assert_lc "F34 candidates list.bend"           research/candidates/mathlib-0.2/list.bend 100 "19 laws: 19 ✓ · 0 ✗ · 0 ~ · 0 !"
  assert_lc "F34 candidates list_templates.bend" research/candidates/mathlib-0.2/list_templates.bend 100 "7 laws: 7 ✓ · 0 ✗ · 0 ~ · 0 !"
  # F32 — every bend-mathlib module is lawcheck-clean (0 counterexamples, 0 checker errors).
  # Full-strength F32 (100 instances) is the pinned CI gate; 50 matches the nightly nat check.
  local m
  for m in all bool equal list nat; do
    assert_lc "F32 packages/bend-mathlib/$m.bend clean" "packages/bend-mathlib/$m.bend" 50 "0 ✗" "0 !"
  done
}

self_test() {
  printf '# run.sh --self-test: proving the harness can fail on a perturbed fact\n'
  local tmp rc=0 saved
  tmp="$(mktemp -d)"
  mkdir -p "$tmp/review2"
  # Plant a perturbed copy: the file asserted to PASS contains the NON-erased variant
  # (t1b), so the assertion must be reported as a mismatch.
  cp "$SCRIPT_DIR/review2/t1b_nonerased.bend" "$tmp/review2/t1a_erased.bend"
  printf '  -- planted negative: perturbed t1a must not satisfy its assertion\n'
  saved="$EXP_ROOT"; EXP_ROOT="$tmp"
  if assert_bend "planted-negative perturbed file" review2/t1a_erased.bend 0 "All terms check."; then
    printf '  FAIL  self-test: perturbed file satisfied the assertion\n'
    rc=1
  else
    printf '  ok    self-test: perturbation was detected\n'
  fi
  EXP_ROOT="$saved"
  printf '  -- planted negative: wrong expected exit on the real t1a must not satisfy\n'
  if assert_bend "planted-negative wrong exit" review2/t1a_erased.bend 1 "All terms check."; then
    printf '  FAIL  self-test: wrong expectation accepted\n'
    rc=1
  else
    printf '  ok    self-test: wrong expectation detected\n'
  fi
  printf '  -- positive control: the real t1a must satisfy its assertion\n'
  if assert_bend "control t1a" review2/t1a_erased.bend 0 "All terms check."; then
    :
  else
    printf '  FAIL  self-test: positive control failed\n'
    rc=1
  fi
  if [ "$rc" -eq 0 ]; then
    printf '# self-test passed: harness detects perturbation and wrong expectations\n'
  else
    printf '# self-test FAILED\n'
  fi
  return "$rc"
}

if [ "${1:-}" = "--self-test" ]; then
  self_test
  exit $?
fi

suite
printf '\n# %d passed, %d failed\n' "$PASS" "$FAIL"
[ "$FAIL" -eq 0 ] || exit 1
exit 0

# --- Explicit non-goals (facts with no definable local assertion) ---------------------
# F1  hub name/version grammar and publication ownership: needs the hub and a publisher login.
# F2  publish bundles local imports, never hub imports: source-level (`main.ts pkg_files`).
# F6  Base names all `Type.verb`: a source grep, not a runtime outcome; churn is guarded by F5.
# F9  1,600-lemma import time/memory: a timing measurement, not a stable assertion.
# F14 function-typed hypotheses in live code (Bend 2.1 / issue #848): not implemented; no file.
# F15 `import 0x<hash>/f.bend` from the hub: needs network and a warm hub cache.
# F17 `--check-only` exists: exercised by every assertion above (no separate fact).
# F18 unsafe/foreign reliance is reported by name: no @unsafe fixture in research/;
#     `tools/mathlib/check.ts` enforces the exact `All terms check.` verdict instead.
# F19 publish refuses open laws/holes: requires `bend publish` and a hub login.
# F20 installer sha256 / `bend version` / BEND_NO_TELEMETRY: the CI install step already pins
#     version+sha256 in toolchain.json.
# F23 `bend.ts` loads under Bun and lists declarations: covered by the nightly
#     `bun test tools/reader tools/lawcheck` step in .github/workflows/ci.yml.
# F30 `bun build --compile` lawcheck binary: a packaging build, out of scope here.
# F33 a single @unsafe fill still prints `All terms check.` (issue #1001): reproducing a known
#     checker bug is not a design invariant; docs' source cross-check covers it.
