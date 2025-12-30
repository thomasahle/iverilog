# UVM Support Plan for Icarus Verilog

## Goal
Enable full UVM testbench support for the mbits-mirafra verification IP blocks.

## AVIP Compilation & Runtime Status

| AVIP | Compiles | Runs | Notes |
|------|----------|------|-------|
| APB | ✅ | ✅ | Full testbench runs, UVM phases execute |
| UART | ✅ | ✅ | Full testbench runs, UVM phases execute |
| AHB | ✅ | ✅ | Full testbench runs, UVM phases execute |
| AXI4 | ❌ | ❌ | Uses unsupported assoc array patterns (see Known Issues) |
| SPI | ❌ | ❌ | Needs multi-dimensional struct array indexing + variable index |
| I2S | ❌ | ❌ | Multiple issues: unpacked array struct members, nested .size(), constructor args |
| I3C | ❌ | ❌ | Same unpacked array struct issues as I2S |
| JTAG | ❌ | ❌ | Syntax error with inline randomize() constraints |
| AXI4-Lite | 🔄 | 🔄 | Complex project structure, needs dedicated compile setup |

## Completed Features

### Phase 1: Core Class Support ✅
- [x] Class definitions and instantiation
- [x] Class inheritance and polymorphism
- [x] Virtual methods and method dispatch
- [x] Class properties (scalar and array)
- [x] `$cast` system function for class hierarchy
- [x] `this` pointer in class methods

### Phase 2: Container Types ✅
- [x] Queues of class objects
- [x] Dynamic arrays of class objects
- [x] Associative arrays with class values
- [x] Queue methods: push_back, push_front, pop_back, pop_front, size

### Phase 3: Concurrent Execution ✅
- [x] fork/join_none in class tasks
- [x] `this` preservation across fork context switches
- [x] Process spawning from class methods

### Phase 4: Coverage ✅
- [x] Basic covergroup declarations
- [x] sample() method with typed arguments (generates no-op)
- [x] get_coverage() method returning coverage percentage

### Phase 5: Interface Support ✅
- [x] Interface port declarations
- [x] Interface arrays in generate blocks
- [x] Parameterized interface signal widths
- [x] VVP comparison width mismatch fix for case statements

### Phase 6: foreach on Class Properties ✅
- [x] foreach on packed vector class properties (logic [N-1:0] data)
- [x] foreach on queue class properties
- [x] Support for this.property and property syntax

### Phase 7: Event and Struct Support ✅
- [x] Event class property access and assignment
- [x] Symbol resolution priority (class properties before standalone events)
- [x] Dynamic bit-select on packed struct members
- [x] Struct element access from queue class properties

### Phase 8: UVM Infrastructure ✅
- [x] uvm_pkg stub with core UVM classes
- [x] Factory pattern (uvm_factory, create_by_name)
- [x] UVM phases (build, connect, run, etc.)
- [x] Configuration database (uvm_config_db)
- [x] Analysis ports and FIFOs
- [x] Sequence/sequencer infrastructure
- [x] run_test() implementation

### Phase 9: Display Formatting ✅
- [x] %p format specifier for $sformatf/$display

## Current Warnings (Non-Blocking)

These warnings appear during compilation but don't prevent operation:

1. **Extern function declarations** - Parsed but out-of-body definitions not linked
2. **Constraint declarations** - Parsed but randomization constraints not enforced
3. **Unpacked structs** - Parsed but not fully supported in all contexts

## Known Issues

1. **bind directive** - Parses correctly but not implemented (shows warning, ignored)
2. **AXI4 associative array patterns** - The AXI4 AVIP uses unsupported patterns:
   - Associative arrays with additional unpacked dimensions: `bit [W-1:0] data[int][1]`
   - Bit selects into associative array elements: `data[key][idx][bit] = 1'b1`
   - These patterns cause compile-time assertion failures in dimension handling
3. **SPI multi-dimensional indexing** - `data[i][j:k]` where `i` is variable requires workaround:
   - Iverilog requires all but the last index to be constant
   - **Workaround**: Extract to temp first: `temp = data[i]; result = temp[j:k];`
4. **I2S unpacked struct member access** - Indexed access to unpacked array struct members with variable index not supported
5. **Dynamic array .size() on nested properties** - `obj.prop.arr.size()` returns 0 (deferred elaboration)

## Pending Features

### Phase 10: Enhanced Randomization
- [ ] Constraint solver for class constraints
- [ ] Inline constraints with randomize() { ... }
- [ ] Soft constraints
- [ ] dist constraints for weighted distributions

### Phase 11: Extern Functions/Tasks
- [ ] Out-of-body function definitions
- [ ] Out-of-body task definitions
- [ ] Method prototyping with extern keyword

### Phase 12: SystemVerilog Assertions (SVA)
- [ ] Property declarations (use -gno-assertions to disable)
- [ ] Concurrent assertions
- [ ] bind directive

### Phase 13: Advanced Features
- [ ] Full unpacked struct support
- [ ] Multi-dimensional indexed struct member access
- [ ] Coverpoints with full bins support
- [ ] Cross coverage

## Testing Strategy
- Unit tests for each feature in ivtest/ivltests/
- Integration tests with mbits-mirafra AVIPs
- Regular commits after each feature implementation
- Use -gno-assertions flag until SVA support is complete

## Recent Changes
- 2025-12-30: Fixed string select for struct member access in associative array keys (AHB now works)
- 2025-12-30: Tested all AVIPs - APB, UART, AHB working, others need specific features
- 2025-12-30: Identified specific blockers for AXI4, SPI, I2S AVIPs
- 2025-12-30: Fixed parameterized class specialization scope lookup (UART now runs)
- 2025-12-30: Added bind directive parsing for module+interface combinations
- 2025-12-30: Added %p format specifier for $sformatf/$display
- 2025-12-30: APB, UART, and AHB AVIPs run full UVM testbenches
- 2025-12-30: Added covergroup sample() typed argument support
- 2025-12-30: Fixed event class property resolution

## Next Priority
1. Test I2S AVIP and identify specific blockers
2. Implement extern function out-of-body definitions
3. Test remaining AVIPs (I3C, JTAG, AXI4-Lite)
4. Add support for assoc arrays with unpacked dimensions (for AXI4)
