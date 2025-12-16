// Test fork/join_none with virtual method dispatch
// This tests fork_this with %fork/virt opcode

class Base;
  int value;

  function new(int v);
    value = v;
  endfunction

  virtual task run();
    fork
      do_work();
    join_none
  endtask

  virtual task do_work();
    value = value + 1;
    $display("Base::do_work: value = %0d", value);
  endtask
endclass

class Derived extends Base;
  function new(int v);
    super.new(v);
  endfunction

  virtual task do_work();
    // Override - should be called via virtual dispatch
    value = value * 2;
    helper();
    $display("Derived::do_work: value = %0d", value);
  endtask

  function void helper();
    // Nested function call from virtual method
    value = value + 100;
  endfunction
endclass

module test;
  initial begin
    Base b;
    Derived d;

    // Test with derived class
    d = new(5);
    $display("Initial derived: value = %0d", d.value);
    d.run();
    #1;

    // Expected: 5 * 2 + 100 = 110
    if (d.value !== 110) begin
      $display("FAILED: expected derived value=110, got %0d", d.value);
      $finish;
    end

    // Test with base class
    b = new(10);
    $display("Initial base: value = %0d", b.value);
    b.run();
    #1;

    // Expected: 10 + 1 = 11
    if (b.value !== 11) begin
      $display("FAILED: expected base value=11, got %0d", b.value);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
