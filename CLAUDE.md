# Icarus Verilog Development Notes

## VVP Process Management - CRITICAL

When running VVP simulations:

1. **Always use `timeout --kill-after=5`** or run with proper process group killing. The basic `timeout` command only kills the direct child, not the actual `vvp` process when piped through `tail` or `head`.

2. **Disable waveform dumping for test runs** - VVP tests with `$dumpfile`/`$dumpvars` can generate massive VCD files (100GB+) if left running.

3. **After any timeout, check for orphan vvp processes:**
   ```bash
   ps aux | grep vvp | grep -v grep
   pkill -9 vvp  # if needed
   ```

4. **Clean up waveform files after tests:**
   ```bash
   find /Users/ahle/repos -name "*.vcd" -size +10M -delete
   ```

## Safe Test Running Pattern

```bash
# Use timeout with process group kill
timeout --foreground 30 vvp test.vvp 2>&1 | tail -40

# Or run without piping and capture output
timeout 30 vvp test.vvp > output.log 2>&1; tail -40 output.log

# Always clean up after
rm -f waveform.vcd *.vcd
```

## Disk Space Monitoring

Large space consumers to watch:
- `*.vcd` waveform files (can grow to 100GB+)
- `.lake/` directories (Lean 4 builds, 7GB+)
- `.claude/projects/` conversation logs
- `/var/folders/` Metal shader caches
