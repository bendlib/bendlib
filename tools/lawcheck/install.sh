#!/bin/sh
# Install the lawcheck binary for this machine from a bendlib GitHub release, checked against the
# release's SHA256SUMS.
#
#   curl -fsSL https://raw.githubusercontent.com/bendlib/bendlib/main/tools/lawcheck/install.sh | sh
#
# LAWCHECK_VERSION=0.3.0 picks a release (default: the newest lawcheck-v* release);
# LAWCHECK_DIR=/usr/local/bin picks where it goes (default: ~/.local/bin).
set -eu

REPO="bendlib/bendlib"
DIR="${LAWCHECK_DIR:-$HOME/.local/bin}"

say() { printf 'lawcheck install: %s\n' "$*" >&2; }
die() { say "$*"; exit 1; }

case "$(uname -s)" in
  Linux) os=linux ;;
  Darwin) os=darwin ;;
  *) die "no lawcheck binary for $(uname -s); run it from source: bun tools/lawcheck/cli.ts" ;;
esac
case "$(uname -m)" in
  x86_64|amd64) arch=x64 ;;
  arm64|aarch64) arch=arm64 ;;
  *) die "no lawcheck binary for $(uname -m)" ;;
esac

command -v curl >/dev/null 2>&1 || die "needs curl"

if [ -n "${LAWCHECK_VERSION:-}" ]; then
  tag="lawcheck-v${LAWCHECK_VERSION#v}"
else
  # the repository's latest release may be a bend-mathlib one, so pick the newest lawcheck tag
  tag=$(curl -fsSL "https://api.github.com/repos/$REPO/releases?per_page=100" \
    | grep -o '"tag_name": *"lawcheck-v[^"]*"' | head -n 1 | sed 's/.*"\(lawcheck-v[^"]*\)"/\1/') \
    || die "cannot list releases of $REPO (set LAWCHECK_VERSION to skip the lookup)"
  [ -n "$tag" ] || die "no lawcheck release found in $REPO"
fi

asset="lawcheck-$os-$arch"
base="https://github.com/$REPO/releases/download/$tag"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT INT TERM

say "downloading $asset from $tag"
curl -fsSL -o "$tmp/$asset" "$base/$asset" || die "cannot download $base/$asset"
curl -fsSL -o "$tmp/SHA256SUMS" "$base/SHA256SUMS" || die "cannot download $base/SHA256SUMS"

want=$(grep " $asset\$" "$tmp/SHA256SUMS" | cut -d' ' -f1)
[ -n "$want" ] || die "SHA256SUMS of $tag has no line for $asset"
if command -v sha256sum >/dev/null 2>&1; then
  have=$(sha256sum "$tmp/$asset" | cut -d' ' -f1)
else
  have=$(shasum -a 256 "$tmp/$asset" | cut -d' ' -f1)
fi
[ "$have" = "$want" ] || die "checksum mismatch for $asset: got $have, SHA256SUMS says $want"

mkdir -p "$DIR"
chmod +x "$tmp/$asset"
[ "$os" = darwin ] && xattr -d com.apple.quarantine "$tmp/$asset" 2>/dev/null || true
mv "$tmp/$asset" "$DIR/lawcheck"
say "installed $("$DIR/lawcheck" --version) to $DIR/lawcheck"

case ":$PATH:" in
  *":$DIR:"*) ;;
  *) say "$DIR is not on your PATH; add it, e.g.: export PATH=\"$DIR:\$PATH\"" ;;
esac
if ! command -v bend >/dev/null 2>&1 && [ ! -x "$HOME/.bend/bin/bend" ]; then
  say "lawcheck runs the bend checker, which is not installed: curl -fsSL https://bend-lang.com/install.sh | sh"
fi
