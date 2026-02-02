---
name: coq-timeout-warning
enabled: true
event: bash
pattern: coqc|coqtop
---

**Coq Compilation Best Practices**

When running Coq commands, always:

1. **Use timeout** to prevent runaway processes:
   ```bash
   timeout 120 coqc -Q NINE65 NINE65 NINE65/File.v
   ```

2. **Check for stuck processes** after parallel runs:
   ```bash
   ps aux | grep coqc | grep -v grep
   ```

3. **Kill orphans** if found:
   ```bash
   pkill -9 -f coqc 2>/dev/null || true
   ```

This prevents resource exhaustion during formalization swarm parallel agent runs.
