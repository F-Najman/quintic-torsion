#!/usr/bin/env bash
# Re-run the jobs from the repository root and compare their logs with git diff.
# Usage: ./verify_all.sh [-j JOBS] [LOG_PATH_FILTER]
# A full run costs roughly 200 CPU hours; start with a subset.
# Exit 0 means all selected jobs passed their completion and result checks.
# Failed jobs give a nonzero status (their count, capped at 125).
set -uo pipefail

usage_error() {
    echo "ERROR: $*" >&2
    echo "Usage: ./verify_all.sh [-j JOBS] [LOG_PATH_FILTER]" >&2
    exit 2
}

JOBS=1
while getopts "j:" opt; do
    case $opt in j) JOBS=$OPTARG;; *) usage_error "invalid option";; esac
done
shift $((OPTIND-1))
[[ $JOBS =~ ^[1-9][0-9]*$ ]] || usage_error "-j requires a positive integer"
[ "$#" -le 1 ] || usage_error "expected at most one log-path filter"
FILTER="${1:-}"
[ -r jobs.txt ] || usage_error "jobs.txt is missing or unreadable; run from the repository root"

# Validate the whole manifest before overwriting any logs. The fourth column is optional.
JOB_RE=$'^([^\t]+)\t([^\t]+)\t([^\t]+)(\t([^\t]+))?$'
declare -A SEEN=()
ALL=(); SEL=(); NEED_MAGMA=0; LINE=0
while IFS= read -r job || [ -n "$job" ]; do
    LINE=$((LINE+1))
    [[ $job =~ ^[[:space:]]*(#|$) ]] && continue
    [[ $job =~ $JOB_RE ]] || usage_error "jobs.txt:$LINE: expected three or four tab-separated fields"
    log=${BASH_REMATCH[1]}; cmd=${BASH_REMATCH[2]}; marker=${BASH_REMATCH[3]}
    expected=${BASH_REMATCH[5]:-}
    [ -z "${SEEN[$log]+present}" ] || usage_error "jobs.txt:$LINE: duplicate log path $log"
    SEEN[$log]=1
    if [ -n "$expected" ]; then
        rc=0; grep -E -- "$expected" < /dev/null > /dev/null || rc=$?
        [ "$rc" -le 1 ] || usage_error "jobs.txt:$LINE: invalid result expression"
    fi
    ALL+=("$job")
    if [[ -z $FILTER || $log == *"$FILTER"* ]]; then
        SEL+=("$job")
        [[ $cmd == magma\ * ]] && NEED_MAGMA=1
    fi
done < jobs.txt
[ "${#ALL[@]}" -gt 0 ] || usage_error "jobs.txt contains no jobs"
[ "${#SEL[@]}" -gt 0 ] || usage_error "no log path matches '$FILTER'"

if [ "$NEED_MAGMA" -eq 1 ]; then
    command -v magma > /dev/null || usage_error "magma is not on PATH"
    for d in mdmagma/v2/mdmagma.spec mdmagma/Magma/magma.spec gl2/magma.spec fast_hecke.m; do
        [ -r "$d" ] && continue
        echo "Missing $d. Initialise the pinned packages from the repository root:" >&2
        echo "    git submodule update --init" >&2
        echo "    git -C mdmagma submodule update --init Magma" >&2
        exit 1
    done
fi

STATUSDIR=$(mktemp -d) || exit 1
trap 'rm -rf -- "$STATUSDIR"' EXIT
export STATUSDIR

last_line() { grep -av '^[[:space:]]*$' "$1" | tail -1; }
fail_job() {
    local record
    echo "!!! $2"
    record=$(mktemp "$STATUSDIR/fail.XXXXXX") || return 1
    printf '%s\n' "$1" > "$record"
    return 1
}
run_one() {
    local log cmd marker expected rc last
    IFS=$'\t' read -r log cmd marker expected <<< "$1"
    mkdir -p "$(dirname "$log")" || { fail_job "$log" "cannot create log directory: $log"; return 1; }
    echo "==> $log : $cmd"
    rc=0; (eval "$cmd") > "$log" 2>&1 || rc=$?
    [ "$rc" -eq 0 ] || { fail_job "$log" "FAILED (exit $rc): $log"; return 1; }
    last=$(last_line "$log")
    if [[ $last != "$marker" && $last != "$marker "* ]]; then
        fail_job "$log" "INCOMPLETE: $log should end in '$marker', last line is '${last:-<empty>}'"
        return 1
    fi
    if [ -n "$expected" ] && ! grep -aEq -- "$expected" "$log"; then
        fail_job "$log" "UNEXPECTED RESULT: $log does not match '$expected'"
        return 1
    fi
    mktemp "$STATUSDIR/ok.XXXXXX" > /dev/null
}
export -f last_line fail_job run_one

# mdmagma's spec includes its pinned Sutherland package. Initialise the separate GL2
# version in another process. Warm up fast_hecke.m too, before several shards attach it.
init_packages() {
    local spec rc last
    echo "==> initialising the Magma packages"
    for spec in mdmagma/v2/mdmagma.spec gl2/magma.spec; do
        {
            printf 'SetColumns(0);\nAttachSpec("%s");\n' "$spec"
            [ "$spec" != mdmagma/v2/mdmagma.spec ] || printf 'Attach("fast_hecke.m");\n'
            printf 'print "PACKAGE_READY";\nquit;\n'
        } > "$STATUSDIR/init.m" || return 1
        echo "    $spec"
        rc=0; magma -n -b "$STATUSDIR/init.m" > "$STATUSDIR/init.log" 2>&1 || rc=$?
        last=$(last_line "$STATUSDIR/init.log")
        if [ "$rc" -ne 0 ] || [ "$last" != PACKAGE_READY ]; then
            echo "!!! could not attach $spec (exit $rc):" >&2
            tail -20 "$STATUSDIR/init.log" >&2
            return 1
        fi
    done
}

echo "${#SEL[@]} of ${#ALL[@]} jobs selected; $JOBS at a time"
if [ "$NEED_MAGMA" -eq 1 ]; then init_packages || exit 1; fi

RUN_STATUS=0
if [ "$JOBS" = 1 ]; then
    for job in "${SEL[@]}"; do run_one "$job" || RUN_STATUS=$?; done
else
    printf '%s\n' "${SEL[@]}" | xargs -d '\n' -P "$JOBS" -I{} bash -uo pipefail -c 'run_one "$@"' _ {} || RUN_STATUS=$?
fi

shopt -s nullglob
FAILED=("$STATUSDIR"/fail.*); PASSED=("$STATUSDIR"/ok.*)
NFAIL=${#FAILED[@]}
MISSING=$((${#SEL[@]}-${#FAILED[@]}-${#PASSED[@]}))
if [ "$MISSING" -ne 0 ]; then
    echo "!!! execution did not record a result for every selected job" >&2
    [ "$MISSING" -gt 0 ] && NFAIL=$((NFAIL+MISSING)) || NFAIL=$((NFAIL+1))
elif [ "$RUN_STATUS" -ne 0 ] && [ "$NFAIL" -eq 0 ]; then
    echo "!!! job execution failed (exit $RUN_STATUS)" >&2
    NFAIL=1
fi
if [ "$NFAIL" -gt 0 ]; then
    echo "$NFAIL of ${#SEL[@]} jobs failed:"
    [ "${#FAILED[@]}" -eq 0 ] || sort "${FAILED[@]}" | sed 's/^/    /'
    [ "$NFAIL" -le 125 ] || NFAIL=125
    exit "$NFAIL"
fi
echo "all ${#SEL[@]} jobs completed; now run  git diff  to compare with the committed logs"
