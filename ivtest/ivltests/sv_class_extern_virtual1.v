// Test virtual dispatch with extern methods
// Extern virtual methods should dispatch to derived class overrides
// This tests that the virtual qualifier is properly propagated from
// extern declarations to out-of-body method definitions.

class Base;
  int value;

  function new();
    value = 10;
  endfunction

  // Extern virtual method declaration
  extern virtual function int compute();

  // Wrapper method that calls virtual method
  function int do_compute();
    return compute();
  endfunction
endclass

// Out-of-body definition - should inherit virtual qualifier
function int Base::compute();
  return value;
endfunction

class Derived extends Base;
  function new();
    super.new();
    value = 20;
  endfunction

  // Override the virtual method
  virtual function int compute();
    return value * 2;  // Returns 40
  endfunction
endclass

module test;
  initial begin
    Base b;
    Derived d;
    Base ref_to_d;
    int result;
    int pass;

    pass = 1;

    // Test 1: Direct call on base object
    b = new;
    result = b.compute();
    if (result !== 10) begin
      $display("FAILED: Base.compute() returned %0d, expected 10", result);
      pass = 0;
    end

    // Test 2: Direct call on derived object
    d = new;
    result = d.compute();
    if (result !== 40) begin
      $display("FAILED: Derived.compute() returned %0d, expected 40", result);
      pass = 0;
    end

    // Test 3: Polymorphic call through base reference
    ref_to_d = d;
    result = ref_to_d.compute();
    if (result !== 40) begin
      $display("FAILED: (Base ref).compute() on Derived returned %0d, expected 40", result);
      pass = 0;
    end

    // Test 4: Polymorphic call through wrapper method
    result = ref_to_d.do_compute();
    if (result !== 40) begin
      $display("FAILED: (Base ref).do_compute() returned %0d, expected 40", result);
      pass = 0;
    end

    if (pass)
      $display("PASSED");

    $finish;
  end
endmodule
