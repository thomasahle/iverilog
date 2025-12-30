// Test event class property access and assignment
// This tests that events declared as class properties can be:
// 1. Accessed within class methods (implicit this.event)
// 2. Assigned to other event properties

class Container;
  event myEvent;
endclass

class Outer;
  Container inner;
  event synchronizer;

  function new();
    inner = new();
  endfunction

  function void test_event_assignment();
    // Assign event property to another object's event property
    // This is legal in SystemVerilog - events can be aliased
    inner.myEvent = synchronizer;
    $display("PASSED: Event property assignment compiles");
  endfunction
endclass

module test;
  Outer obj;

  initial begin
    obj = new();
    obj.test_event_assignment();
  end
endmodule
