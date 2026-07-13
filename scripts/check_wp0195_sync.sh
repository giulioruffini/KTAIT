#!/usr/bin/env bash
# Deprecated name. The check now covers WP0195 *and* every paper that cites KTAIT
# by name, plus a sorry-free guard. See scripts/check_sync.sh.
exec "$(dirname "$0")/check_sync.sh" "$@"
