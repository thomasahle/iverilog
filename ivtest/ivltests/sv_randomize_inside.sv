// Test randomize() with 'inside' constraints
// The 'inside' constraint should restrict random values to a specified range
//
// Author: Claude (Anthropic)

class InlineConstraintTest;
  rand int value;
  rand int limited;
  rand int bounded;

  function new();
    value = 0;
    limited = 0;
    bounded = 0;
  endfunction
endclass

module test;
  InlineConstraintTest obj;
  int pass_count = 0;
  int fail_count = 0;
  int i;

  initial begin
    obj = new();

    // Test 1: inside constraint with range [10:20]
    $display("Test 1: inside {[10:20]}");
    pass_count = 0;
    for (i = 0; i < 10; i = i + 1) begin
      if (obj.randomize() with { limited inside {[10:20]}; }) begin
        if (obj.limited >= 10 && obj.limited <= 20) begin
          pass_count = pass_count + 1;
        end else begin
          $display("FAILED: limited=%0d not in [10:20]", obj.limited);
          fail_count = fail_count + 1;
        end
      end else begin
        $display("FAILED: randomize returned 0");
        fail_count = fail_count + 1;
      end
    end
    if (pass_count == 10)
      $display("  PASSED: All 10 randomizations in [10:20]");

    // Test 2: inside constraint with range [0:100]
    $display("Test 2: inside {[0:100]}");
    pass_count = 0;
    for (i = 0; i < 10; i = i + 1) begin
      if (obj.randomize() with { bounded inside {[0:100]}; }) begin
        if (obj.bounded >= 0 && obj.bounded <= 100) begin
          pass_count = pass_count + 1;
        end else begin
          $display("FAILED: bounded=%0d not in [0:100]", obj.bounded);
          fail_count = fail_count + 1;
        end
      end else begin
        $display("FAILED: randomize returned 0");
        fail_count = fail_count + 1;
      end
    end
    if (pass_count == 10)
      $display("  PASSED: All 10 randomizations in [0:100]");

    // Test 3: inside constraint with negative range [-50:50]
    $display("Test 3: inside {[-50:50]}");
    pass_count = 0;
    for (i = 0; i < 10; i = i + 1) begin
      if (obj.randomize() with { value inside {[-50:50]}; }) begin
        if (obj.value >= -50 && obj.value <= 50) begin
          pass_count = pass_count + 1;
        end else begin
          $display("FAILED: value=%0d not in [-50:50]", obj.value);
          fail_count = fail_count + 1;
        end
      end else begin
        $display("FAILED: randomize returned 0");
        fail_count = fail_count + 1;
      end
    end
    if (pass_count == 10)
      $display("  PASSED: All 10 randomizations in [-50:50]");

    // Summary
    if (fail_count == 0) begin
      $display("PASSED: All inside constraint tests passed");
    end else begin
      $display("FAILED: %0d tests failed", fail_count);
    end
  end
endmodule
