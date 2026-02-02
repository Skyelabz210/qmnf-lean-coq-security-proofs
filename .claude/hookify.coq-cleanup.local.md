---
name: coq-process-cleanup
enabled: true
event: stop
pattern: .*
---

**Coq Process Cleanup Reminder**

Before stopping, if you ran any Coq compilation commands (`coqc`, `coqtop`, `coqide`), ensure all processes completed or were terminated:

```bash
pkill -9 -f "coqc|coqtop" 2>/dev/null || true
```

This prevents zombie Coq processes from accumulating during formalization swarm runs.

**Checklist:**
- [ ] All `coqc` compilations completed or killed
- [ ] No background Coq processes left running
- [ ] System resources freed
