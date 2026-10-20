#!/bin/bash
# Print a Python that has the pipeline's packages (numpy, torch, yaml): the
# pipeline's venv if one is next to the repository, else python3.
#
#     scripts/find_python.sh <repo>
REPO="${1:?usage: scripts/find_python.sh <repo>}"
for py in "$REPO/.venv/bin/python" "$REPO/venv/bin/python" "$REPO/../.venv/bin/python" \
          "$REPO/../venv/bin/python" "$HOME/venv/bin/python" "$(command -v python3)"; do
  if [ -x "$py" ] && "$py" -c "import numpy, torch, yaml" 2>/dev/null; then
    echo "$py"
    exit 0
  fi
done
echo "no Python with numpy, torch and yaml found: activate the pipeline's venv and use python3" >&2
exit 1
