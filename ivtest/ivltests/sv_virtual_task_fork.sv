// Test virtual task dispatch within fork/join_none
// This is critical for UVM testbenches where do_run_phase()
// forks this.run_phase() and expects virtual dispatch to work

class Base;
  virtual task run();
    $display("FAILED: Base::run called instead of Derived::run");
  endtask

  task do_run();
    fork
      this.run();
    join_none
  endtask
endclass

class Derived extends Base;
  virtual task run();
    $display("PASSED: Derived::run called correctly");
  endtask
endclass

module test;
  initial begin
    Derived d = new();

    // Direct call should work
    $display("Test 1: Direct call d.run()");
    d.run();

    // Call via do_run which forks this.run() - this is the critical test
    $display("Test 2: Call d.do_run() which forks this.run()");
    d.do_run();

    #1;  // Wait for fork to execute

    $finish;
  end
endmodule
