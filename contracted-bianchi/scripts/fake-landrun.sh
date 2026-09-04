#!/usr/bin/env bash
set -euo pipefail

# Development-only macOS fallback.  CI and hosted verification must use real
# Landrun; this shim is accepted only when the caller explicitly opts in.
value_flags=(--ro --rox --rw --rwx --bind-tcp --connect-tcp --log-level --env)

is_value_flag() {
  local flag=$1
  for value_flag in "${value_flags[@]}"; do
    [ "$flag" = "$value_flag" ] && return 0
  done
  return 1
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --)
      shift
      break
      ;;
    -*)
      if is_value_flag "$1"; then
        [ "$#" -ge 2 ] || { echo "fake-landrun: missing value for $1" >&2; exit 2; }
        shift
      fi
      shift
      ;;
    *)
      break
      ;;
  esac
done

[ "$#" -gt 0 ] || { echo "fake-landrun: no command given" >&2; exit 2; }
echo "WARNING: using the explicit unsandboxed macOS Landrun fallback" >&2
exec "$@"
