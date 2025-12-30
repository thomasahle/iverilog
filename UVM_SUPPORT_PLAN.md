# UVM Support Plan for Icarus Verilog

## Goal
Enable full UVM testbench support for the mbits-mirafra verification IP blocks.

## AVIP Compilation & Runtime Status

| AVIP | Compiles | Runs | Notes |
|------|----------|------|-------|
| APB | ✅ | ✅ | Full testbench runs, UVM phases execute |
| AXI4 | ✅ | 🔄 | Pending runtime test |
| SPI | ✅ | 🔄 | Pending runtime test |
| UART | ✅ | 🔄 | Pending runtime test |
| I2S | ✅ | 🔄 | Pending runtime test |
| AHB | ✅ | 🔄 | Pending runtime test |
| I3C | ✅ | 🔄 | Pending runtime test |
| JTAG | 🔄 | 🔄 | Pending test |
| AXI4-Lite | 🔄 | 🔄 | Pending test |

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

## Current Warnings (Non-Blocking)

These warnings appear during compilation but don't prevent operation:

1. **Extern function declarations** - Parsed but out-of-body definitions not linked
2. **Constraint declarations** - Parsed but randomization constraints not enforced
3. **Unpacked structs** - Parsed but not fully supported in all contexts
4. **`%p` format specifier** - Not supported in $sformatf (prints literal <%p>)

## Pending Features

### Phase 9: Enhanced Randomization
- [ ] Constraint solver for class constraints
- [ ] Inline constraints with randomize() { ... }
- [ ] Soft constraints
- [ ] dist constraints for weighted distributions

### Phase 10: Extern Functions/Tasks
- [ ] Out-of-body function definitions
- [ ] Out-of-body task definitions
- [ ] Method prototyping with extern keyword

### Phase 11: SystemVerilog Assertions (SVA)
- [ ] Property declarations (use -gno-assertions to disable)
- [ ] Concurrent assertions
- [ ] bind directive

### Phase 12: Advanced Features
- [ ] Full unpacked struct support
- [ ] `%p` format specifier for $sformatf
- [ ] Coverpoints with full bins support
- [ ] Cross coverage

## Testing Strategy
- Unit tests for each feature in ivtest/ivltests/
- Integration tests with mbits-mirafra AVIPs
- Regular commits after each feature implementation
- Use -gno-assertions flag until SVA support is complete

## Recent Changes
- 2025-12-30: All 7 main AVIPs compile successfully
- 2025-12-30: APB AVIP runs full UVM testbench
- 2025-12-30: Added covergroup sample() typed argument support
- 2025-12-30: Fixed event class property resolution

## Next Priority
Test remaining AVIPs at runtime and address any blocking issues.
