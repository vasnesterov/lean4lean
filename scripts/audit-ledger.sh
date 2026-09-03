#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")/.."
NAMES="$(python3 scripts/audit-ledger.py --names)"
echo "auditing $(echo "$NAMES" | wc -w) candidate names from the ledger…"
NAMES="$NAMES" lake env lean --run scripts/exists.lean > /tmp/audit-exists.txt 2>/dev/null
python3 scripts/audit-ledger.py --check /tmp/audit-exists.txt
