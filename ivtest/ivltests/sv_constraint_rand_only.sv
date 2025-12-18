// Test: rand-only randomization
// Only properties marked with 'rand' should be randomized
// Non-rand properties should retain their initial values

module test;

  class MyClass;
    rand int rand_value;       // Should be randomized
    int normal_value;          // Should NOT be randomized
    rand bit [7:0] rand_byte;  // Should be randomized
    bit [7:0] normal_byte;     // Should NOT be randomized

    function new();
      rand_value = 100;
      normal_value = 200;
      rand_byte = 8'hAA;
      normal_byte = 8'hBB;
    endfunction
  endclass

  initial begin
    MyClass obj = new();
    int passed = 1;

    // Check initial values
    if (obj.normal_value != 200) begin
      $display("FAIL: normal_value initial value wrong: %0d", obj.normal_value);
      passed = 0;
    end
    if (obj.normal_byte != 8'hBB) begin
      $display("FAIL: normal_byte initial value wrong: %h", obj.normal_byte);
      passed = 0;
    end

    // Randomize
    if (obj.randomize()) begin
      // randomization succeeded
    end

    // Check that non-rand properties still have original values
    if (obj.normal_value != 200) begin
      $display("FAIL: normal_value changed after randomize: %0d (expected 200)", obj.normal_value);
      passed = 0;
    end
    if (obj.normal_byte != 8'hBB) begin
      $display("FAIL: normal_byte changed after randomize: %h (expected BB)", obj.normal_byte);
      passed = 0;
    end

    // Rand properties should (likely) have changed
    // Note: There's a very small chance they didn't change by pure coincidence
    $display("rand_value = %0d (was 100)", obj.rand_value);
    $display("rand_byte = %h (was AA)", obj.rand_byte);

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end

endmodule
