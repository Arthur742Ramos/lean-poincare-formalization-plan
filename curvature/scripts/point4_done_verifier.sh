#!/usr/bin/env bash
# =============================================================================
# Point 4 completion VERIFIER daemon.
#
# The infinite campaign driver (/tmp/p4_campaign_inf.sh) stops only when the
# sentinel /tmp/p4_DONE exists. To make sure the campaign can never stop on a
# *false* completion claim, workers are instructed to never create /tmp/p4_DONE
# directly; instead they create /tmp/p4_DONE_REQUEST only after the audit
# certifies closure. This daemon re-runs the FULL audit (with `lake build`) on
# each request and:
#   * audit passes -> creates /tmp/p4_DONE (the campaign then ends legitimately)
#   * audit fails  -> deletes the request, logs a loud false-alarm, campaign
#                     keeps running.
#
# It never deletes a /tmp/p4_DONE it did not create, so a human can still stop
# the campaign manually by touching /tmp/p4_DONE.
#
# Launch (detached):
#   setsid nohup curvature/scripts/point4_done_verifier.sh >/dev/null 2>&1 &
# =============================================================================
export PATH="$HOME/.elan/bin:$PATH"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AUDIT="$SCRIPT_DIR/point4_audit.sh"
LOG=/tmp/p4_done_verifier.log
REQ=/tmp/p4_DONE_REQUEST
DONE=/tmp/p4_DONE

# single-instance guard
if pgrep -f "point4_done_verifier.sh" | grep -qv "^$$\$"; then
  others=$(pgrep -f "point4_done_verifier.sh" | grep -v "^$$\$" | tr '\n' ' ')
  if [ -n "$others" ]; then
    echo "[verifier $(date '+%F %T')] another instance already running ($others); exiting" >> "$LOG"
    exit 0
  fi
fi

echo "[verifier $(date '+%F %T')] started (pid $$); watching $REQ" >> "$LOG"
while true; do
  if [ -f "$REQ" ]; then
    echo "[verifier $(date '+%F %T')] completion request detected — running FULL audit (lake build)..." >> "$LOG"
    if "$AUDIT" --json /tmp/point4_audit_verify.json >> "$LOG" 2>&1; then
      echo "[verifier $(date '+%F %T')] ✅ AUDIT PASSED — Point 4 CLOSED. Creating $DONE; campaign will stop." >> "$LOG"
      touch "$DONE"
      rm -f "$REQ"
    else
      echo "[verifier $(date '+%F %T')] ❌ AUDIT FAILED — false completion claim. Deleting request; campaign CONTINUES." >> "$LOG"
      rm -f "$REQ"
    fi
  fi
  sleep 15
done
