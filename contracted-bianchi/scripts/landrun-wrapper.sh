#!/usr/bin/env bash
set -euo pipefail

# Comparator passes Landrun options followed directly by the sandboxed command.
# The current Landrun CLI needs an explicit outer `--` before that command.
landrun_binary=${PALOMAR_LANDRUN_BIN:?PALOMAR_LANDRUN_BIN must name the Landrun binary}
landrun_options=()

# Refuse flags that would disable part of the sandbox.  Any future widening
# must be reviewed here instead of being inherited from a dependency update.
while [ "$#" -gt 0 ]; do
  case "$1" in
    -unrestricted-*|--unrestricted-*)
      echo "error: refusing sandbox-disabling Landrun option $1" >&2
      exit 2
      ;;
    --best-effort|-ldd|--ldd|-add-exec|--add-exec|--ignore-missing|--log-disable-originating|--log-enable-subprocesses|--log-disable-subdomains)
      landrun_options+=("$1")
      shift
      ;;
    --log-level|--ro|--rox|--rw|--rwx|--unix|--bind-tcp|--connect-tcp|--env)
      if [ "$#" -lt 2 ]; then
        echo "error: Landrun option $1 is missing its value" >&2
        exit 2
      fi
      landrun_options+=("$1" "$2")
      shift 2
      ;;
    -*)
      echo "error: unrecognized Landrun option $1; update landrun-wrapper.sh" >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [ "$#" -eq 0 ]; then
  echo "error: Comparator supplied no sandboxed command" >&2
  exit 2
fi

exec "$landrun_binary" "${landrun_options[@]}" -- "$@"
