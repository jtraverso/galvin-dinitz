#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build --wfail
lake build Challenge
lake env lean Audit.lean
lake comparator --config comparator.json
