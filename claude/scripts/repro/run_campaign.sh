#!/bin/bash
# Run a full 480-instance campaign for ONE configuration, 12-way parallel,
# writing  <config>.csv  with one "relpath,result,duration" line per instance.
#
# Usage:  run_campaign.sh <config>          # config name understood by run_one.sh
#
# The instance list is taken from the benchmark comparison sheet so that the
# rows line up 1:1 with the recorded reference-solver columns.

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
COMPARISON=${COMPARISON:-/home/mudathir/all/paper-fmcad26-liastar/scripts/comparison.csv}
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
xargs -a "$HERE/files.txt" -P "$JOBS" -I{} "$HERE/run_one.sh" "$cfg" {} > "$HERE/$cfg.csv"
echo "wrote $HERE/$cfg.csv" >&2
cut -d, -f2 "$HERE/$cfg.csv" | sort | uniq -c >&2
