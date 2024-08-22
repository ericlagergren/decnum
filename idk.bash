#!/usr/bin/env bash

set -euo pipefail

gather() {
	local mod="${1}"
	cat <<EOF
pub mod ${mod} {
$(<"src/${mod}.rs")
}
EOF
}
gather bid
gather dpd
gather dec128
gather tables
gather util
gather conv
