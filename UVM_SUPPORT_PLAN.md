# UVM Support Plan for Icarus Verilog

## Goal
Enable full UVM testbench support for the mbits-mirafra verification IP blocks:
- APB AVIP ✅ (compiles and runs)
- UART AVIP (in progress - compiles with -gno-assertions)
- I2S AVIP (pending)
- AXI4 AVIP (pending)
- AXI4-Lite AVIP (pending)
- SPI AVIP (pending)
- JTAG AVIP (pending)
- I3C AVIP (pending)

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
- [x] sample() method
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

## In Progress

### Phase 7: Struct and Property Access
- [ ] Dynamic bit-select on struct members (struct.member[i] where i is variable)
- [ ] Inherited class property visibility in subclass methods
- [ ] Property bit-select expressions in class methods (this.data[i])

### Phase 8: Constraint Support
- [ ] Inline constraints with randomize() { ... }
- [ ] Soft constraints
- [ ] Constraint blocks in classes
- [ ] dist constraints for weighted distributions

## Known UART AVIP Errors (with -gno-assertions)
1. `Class UartTxMonitorProxy does not have a property monitorSynchronizer` - inherited property visibility
2. `A reference to a net or variable ('i') is not allowed in a constant expression` - dynamic struct indexing
3. `Too many arguments (2, expecting 1) in call to function` - function signature mismatch
4. `The expression 'data' cannot be implicitly cast to the target type` - type conversion issue

## Pending Features

### Phase 9: Additional UVM Infrastructure
- [ ] TLM port/export connections
- [ ] uvm_analysis_port write() method
- [ ] Sequence/sequencer handshake improvements
- [ ] Configuration database hierarchical paths

### Phase 10: SystemVerilog Assertions (SVA)
- [ ] Property declarations (use -gno-assertions to disable)
- [ ] Concurrent assertions
- [ ] bind directive

### Phase 11: Advanced Features
- [ ] Coverpoints with bins
- [ ] Cross coverage
- [ ] Functional coverage models
- [ ] Assertions in interfaces

## Testing Strategy
- Unit tests for each feature in ivtest/ivltests/
- Integration tests with mbits-mirafra AVIPs
- Regular commits after each feature implementation
- Use -gno-assertions flag until SVA support is complete

## Current Status
Date: 2025-12-30
Last completed: foreach on packed vector and queue class properties
Next priority: Dynamic bit-select on struct members for UART AVIP
