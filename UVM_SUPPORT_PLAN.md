# UVM Support Plan for Icarus Verilog

## Goal
Enable full UVM testbench support for the mbits-mirafra verification IP blocks.

## Current Status: 7/9 AVIPs Working!

| AVIP | Compiles | Runs | Notes |
|------|----------|------|-------|
| APB | ✅ | ✅ | Full testbench runs, UVM phases execute |
| UART | ✅ | ✅ | Full testbench runs, UVM phases execute |
| AHB | ✅ | ✅ | Full testbench runs, UVM phases execute |
| AXI4 | ✅ | ✅ | Full testbench runs, UVM phases execute |
| SPI | ✅ | ✅ | Full testbench runs, UVM phases execute |
| I2S | ✅ | ✅ | Full testbench runs, UVM phases execute |
| I3C | ✅ | ✅ | Full testbench runs, UVM phases execute |
| JTAG | ✅ | 🔄 | Compiles, UVM starts; test sequence loops (test-specific issue) |
| AXI4-Lite | 🔄 | 🔄 | Complex nested VIP structure, requires multi-VIP compile setup |

## Completed Features

### Core Class Support ✅
- Class definitions, inheritance, polymorphism
- Virtual methods and method dispatch
- Class properties (scalar, array, queue, darray)
- `$cast` for class and enum types
- `this` pointer in class methods
- Parameterized classes (type and value parameters)

### Container Types ✅
- Queues of class objects with all methods
- Dynamic arrays of class objects
- Associative arrays with class values
- Nested container access (`obj.prop.arr.size()`)

### Concurrent Execution ✅
- fork/join_none in class tasks
- `this` preservation across fork context switches
- Process spawning from class methods

### Randomization ✅
- `rand`/`randc` property modifiers
- Basic constraints (comparisons, ranges)
- `inside` constraints
- Implication constraints (`cond -> { body }`)
- foreach constraints (static arrays)
- `std::randomize()` with inline constraints
- Inline constraints with local variables

### Coverage ✅
- Covergroup declarations
- sample() method with typed arguments
- get_coverage() method

### Interface Support ✅
- Interface port declarations
- Interface arrays in generate blocks
- Parameterized interface signal widths

### UVM Infrastructure ✅
- uvm_pkg stub with core UVM classes
- Factory pattern (uvm_factory, create_by_name)
- UVM phases (build, connect, run, extract, check, report, final)
- Configuration database (uvm_config_db)
- Analysis ports and FIFOs
- Sequence/sequencer infrastructure
- run_test() implementation
- TLM ports and exports

### Other Features ✅
- `%p` format specifier for $sformatf/$display
- Multi-dimensional variable indexing
- Event class properties
- Struct member access
- wait() statements

## Known Limitations

### Non-Blocking Warnings (can ignore)
1. **Interface port "limited support"** - Works but shows warning
2. **bind directive warnings** - Ignored (assertion modules not compiled)
3. **Test class not found** - run_test() finds class at runtime

### Actual Limitations
1. **Module-level class handles** - Cannot declare class variables at module scope
   - Workaround: Use interface-based BFM pattern or package-level handles
2. **Parameterized class method value specialization** - Methods don't specialize for value params
   - `class Item#(int W=8)` - methods use default W, not specialized value
   - Workaround: Access properties directly, use runtime parameter
3. **extern function out-of-body definitions** - Parsed but not linked
   - Workaround: Define functions inline in class
4. **Full bins coverage** - Covergroups track samples but not bin hits
5. **unique/unique0 case** - VVP ignores these qualifiers (shows "sorry" message)
6. **SVA assertions** - Use `-gno-assertions` flag to disable

## Remaining Work

### Priority 1: JTAG Test Investigation
- Test compiles and UVM starts
- Sequence appears to loop - likely test-specific issue
- May need JTAG testbench fix rather than compiler fix

### Priority 2: AXI4-Lite Setup
- Complex nested VIP structure with multiple sub-VIPs
- Requires proper multi-VIP compile script

### Priority 3: Module-Level Class Handles
```systemverilog
module top;
  MyClass obj;  // Currently unsupported
  initial obj = new();
endmodule
```
- Would enable more BFM patterns
- Requires VVP infrastructure for module-level objects

### Priority 4: Parameterized Method Value Specialization
```systemverilog
class Item#(int W=8);
  bit [W-1:0] data;
  function void set(bit[W-1:0] val);  // Currently always 8 bits
endclass
Item#(16) i; i.set(16'hABCD);  // Truncates to 8 bits
```

### Priority 5: Enhanced Constraint Features
- `soft` constraints
- `dist` for weighted distributions
- More complex constraint expressions

## Testing Strategy
- Unit tests for each feature in `ivtest/ivltests/sv_*.sv`
- Integration tests with mbits-mirafra AVIPs
- Regular commits after each feature
- Use `-gno-assertions` flag until SVA support complete

## Recent Changes
- 2026-01-12: Fixed dynamic array width mismatch assertion crash in VVP
- 2026-01-12: Fixed $cast in uvm_driver.get_next_item() for parameterized type cast
- 2026-01-12: Added unit tests sv_param_class_cast.sv, sv_darray_width_mismatch.sv
- 2026-01-12: Removed debug prints from elaborate.cc
- 2026-01-12: 7 of 9 mbits-mirafra AVIPs now compile and run!
- 2026-01-12: APB 8b_write test runs with actual transactions and scoreboard comparison!
- 2025-12-30: Multiple fixes for struct access, indexing, interface support
