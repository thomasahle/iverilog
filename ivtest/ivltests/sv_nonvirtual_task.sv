// Test non-virtual task dispatch uses static binding
// Non-virtual tasks should be called based on the declared type of the
// handle, not the actual runtime type of the object.
module test;
  class Base;
    task t;
      $display("Base::t called");
    endtask

    function string get_name;
      return "Base";
    endfunction
  endclass

  class Derived extends Base;
    task t;
      $display("Derived::t called");
    endtask

    function string get_name;
      return "Derived";
    endfunction
  endclass

  int passed = 0;
  int failed = 0;

  initial begin
    Base b1, b2;
    Derived d;

    // Test 1: Non-virtual task called on Base handle pointing to Derived object
    // Should call Base::t because t is non-virtual and handle type is Base
    d = new();
    b1 = d;

    $display("Test 1: Non-virtual task on base handle (actual object: Derived)");
    $display("Expected: Base::t called");
    $display("Actual: ");
    b1.t;  // Should print "Base::t called"

    // Test 2: Non-virtual function already works correctly
    $display("\nTest 2: Non-virtual function on base handle");
    $display("Expected: Base");
    $display("Actual: %s", b1.get_name());
    if (b1.get_name() == "Base") begin
      $display("-> PASSED");
      passed++;
    end else begin
      $display("-> FAILED");
      failed++;
    end

    // Test 3: Direct call on Derived handle should call Derived::t
    $display("\nTest 3: Non-virtual task on derived handle");
    $display("Expected: Derived::t called");
    $display("Actual: ");
    d.t;  // Should print "Derived::t called"

    // Test 4: Direct call on Base instance
    b2 = new();  // Create actual Base object
    $display("\nTest 4: Non-virtual task on base handle (actual object: Base)");
    $display("Expected: Base::t called");
    $display("Actual: ");
    b2.t;  // Should print "Base::t called"

    // Summary
    $display("\n=== Summary ===");
    if (failed == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d tests failed", failed);
    end
    $finish;
  end
endmodule
