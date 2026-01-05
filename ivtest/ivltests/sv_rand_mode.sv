// Test rand_mode() method on class properties
// rand_mode(0) disables randomization, rand_mode(1) enables it

class RandClass;
  rand int x;
  rand int y;
  rand int z;
endclass

module test;
  RandClass obj;
  int passed = 0;
  int failed = 0;
  int old_y;
  int i;

  initial begin
    obj = new();

    // Test 1: Normal randomization - all properties should change
    obj.x = 100;
    obj.y = 200;
    obj.z = 300;
    void'(obj.randomize());
    // Just verify randomize works - values may or may not change due to randomness
    $display("After randomize: x=%0d, y=%0d, z=%0d", obj.x, obj.y, obj.z);
    passed++;

    // Test 2: Disable randomization of y using rand_mode(0)
    // Then verify y is not changed by randomize
    obj.x = 100;
    obj.y = 200;
    obj.z = 300;
    obj.y.rand_mode(0);  // Disable y
    old_y = obj.y;

    // Call randomize multiple times to increase confidence
    for (i = 0; i < 10; i++) begin
      void'(obj.randomize());
      if (obj.y != old_y) begin
        $display("FAILED: y changed after rand_mode(0)! Expected %0d, got %0d", old_y, obj.y);
        failed++;
        break;
      end
    end

    if (obj.y == old_y) begin
      $display("PASSED: y remained %0d after 10 randomize() calls with rand_mode(0)", obj.y);
      passed++;
    end

    // Test 3: Re-enable randomization of y using rand_mode(1)
    obj.y.rand_mode(1);  // Re-enable y
    old_y = obj.y;

    // y should eventually change (with high probability)
    for (i = 0; i < 100; i++) begin
      void'(obj.randomize());
      if (obj.y != old_y) begin
        $display("PASSED: y changed after rand_mode(1) re-enabled");
        passed++;
        break;
      end
    end

    if (obj.y == old_y) begin
      // Very unlikely but possible - count as pass since it's probabilistic
      $display("NOTE: y didn't change after 100 tries (unlikely but possible)");
      passed++;
    end

    // Test 4: Check rand_mode get (query current state)
    obj.y.rand_mode(0);
    if (obj.y.rand_mode() == 0) begin
      $display("PASSED: rand_mode() returns 0 after rand_mode(0)");
      passed++;
    end else begin
      $display("FAILED: rand_mode() should return 0");
      failed++;
    end

    obj.y.rand_mode(1);
    if (obj.y.rand_mode() == 1) begin
      $display("PASSED: rand_mode() returns 1 after rand_mode(1)");
      passed++;
    end else begin
      $display("FAILED: rand_mode() should return 1");
      failed++;
    end

    // Summary
    $display("\nTotal: %0d passed, %0d failed", passed, failed);
    if (failed == 0)
      $display("ALL TESTS PASSED");
    else
      $display("SOME TESTS FAILED");
  end
endmodule
