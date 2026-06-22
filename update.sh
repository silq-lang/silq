#!/usr/bin/env bash
set -euo pipefail

SSH_KEY_LIFETIME="${SSH_KEY_LIFETIME:-1h}"

run_update() {
  git submodule update --init --recursive
  git submodule foreach --recursive "git switch master && git pull --ff-only"
  git pull --recurse-submodules
  git submodule update --checkout
}

uses_ssh_remotes() {
  git config --get-regexp '^(remote|submodule)\..*\.url$' 2>/dev/null |
    awk '{print $2}' |
    grep -Eq '^(ssh://|[^/@[:space:]]+@[^/:[:space:]]+:)'
}

if uses_ssh_remotes; then
  if command -v ssh-agent >/dev/null 2>&1; then
    exec ssh-agent -t "$SSH_KEY_LIFETIME" bash -c "
      set -euo pipefail
      export GIT_SSH_COMMAND=\"\${GIT_SSH_COMMAND:-ssh -o AddKeysToAgent=$SSH_KEY_LIFETIME}\"
      $(declare -f run_update)
      run_update
    "
  else
    echo "SSH remotes detected, but ssh-agent is not installed."
    echo "Continuing without ssh-agent; you may be prompted multiple times."
    run_update
  fi
else
  run_update
fi
