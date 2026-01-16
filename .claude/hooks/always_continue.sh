
#!/usr/bin/env bash
set -euo pipefail

# Optional escape hatch: if this file exists, allow Claude to stop normally.
if [[ -f ".claude/ALLOW_STOP" ]]; then
  exit 0
fi

# IMPORTANT: write to stderr so Claude Code captures it as the continuation message
cat >&2 <<'MSG'
Great! please update your plan towards full SV and UVM support.
What limitations do we still have? What features should we build?
Keep testing on ~/repos/mbits-mirafra.
Remember to make unit tests as you go along and implement more features, and commit regularly.
Continue!
MSG

# Exit 2 = "block stopping and continue"
exit 2


