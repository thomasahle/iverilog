// Test pure virtual method syntax parsing
// This tests that `pure virtual` method declarations are accepted

module test;
  // Abstract base class with pure virtual methods
  virtual class Base;
    int value;

    // Pure virtual function with return type
    pure virtual function string describe();

    // Pure virtual function with parameters
    pure virtual function int compute(int a, int b);

    // Pure virtual task
    pure virtual task do_work();

    // Regular non-virtual method
    function void set_value(int v);
      value = v;
    endfunction
  endclass

  // Derived class that would implement the pure virtual methods
  class Derived extends Base;
    function string describe();
      return "Derived class";
    endfunction

    function int compute(int a, int b);
      return a + b;
    endfunction

    task do_work();
      $display("Working...");
    endtask
  endclass

  initial begin
    // Just test that the syntax compiles
    $display("Pure virtual method syntax is accepted");
    $display("PASSED");
  end
endmodule
