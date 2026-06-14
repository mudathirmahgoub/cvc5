#!/bin/bash
# macOS port of repro/run_campaign.sh -- run a full 480-instance campaign for
# ONE configuration, JOBS-way parallel, writing <config>.csv (one
# "relpath,result,duration" line per instance) next to this script.
#
# Usage:  run_campaign.sh <config>
#
# JOBS defaults to 12 to match the Linux report's methodology (12 parallel jobs,
# 100 s timeout, single Normaliz thread each). Override with JOBS=N.

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
COMPARISON=${COMPARISON:-/Users/mahgoubyahia/paper-fmcad26-liastar/scripts/comparison.csv}
JOBS=${JOBS:-12}
cfg="$1"

# one-time: the 480 benchmark paths, in the sheet's row order
if [ ! -f "$HERE/files.txt" ]; then
  python3 - "$COMPARISON" > "$HERE/files.txt" <<'PY'
import pandas as pd, sys
pd.read_csv(sys.argv[1])['cvc5 lazy  filename'].to_csv(sys.stdout, index=False, header=False)
PY
fi

echo "running config '$cfg' on $(wc -l < "$HERE/files.txt") instances, $JOBS-way parallel..." >&2
# BSD/macOS xargs has no -a; read the file list from stdin instead.
xargs -P "$JOBS" -I{} "$HERE/run_one.sh" "$cfg" {} < "$HERE/files.txt" > "$HERE/$cfg.csv"
echo "wrote $HERE/$cfg.csv" >&2
cut -d, -f2 "$HERE/$cfg.csv" | sort | uniq -c >&2
