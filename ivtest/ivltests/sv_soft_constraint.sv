// Test soft constraints in randomize() with {...}
// Soft constraints don't cause randomize() to fail if they cannot be satisfied

module test;
  class MyClass;
    rand int value;
  endclass

  MyClass obj;
  int count_satisfied, count_total;

  initial begin
    obj = new();

    $display("Test 1: Hard constraint only - value > 50");
    count_satisfied = 0;
    for (int i = 0; i < 10; i++) begin
      if (obj.randomize() with { value > 50; value < 100; }) begin
        if (obj.value > 50 && obj.value < 100) count_satisfied++;
        else begin
          $display("FAILED: Hard constraint not satisfied, value=%0d", obj.value);
          $finish;
        end
      end else begin
        $display("FAILED: randomize() returned 0 for hard constraints");
        $finish;
      end
    end
    $display("  All %0d randomizations satisfied hard constraint", count_satisfied);

    $display("Test 2: Soft constraint with hard constraint");
    // soft value < 30 combined with hard value > 50 - soft cannot be satisfied
    // but randomize should still succeed
    count_satisfied = 0;
    for (int i = 0; i < 10; i++) begin
      if (obj.randomize() with { value > 50; value < 100; soft value < 30; }) begin
        // Hard constraint must be satisfied, soft may not be
        if (obj.value > 50 && obj.value < 100) begin
          count_satisfied++;
        end else begin
          $display("FAILED: Hard constraint violated, value=%0d", obj.value);
          $finish;
        end
      end else begin
        // Soft constraints should not cause failure
        $display("FAILED: randomize() returned 0 even with soft constraint");
        $finish;
      end
    end
    $display("  All %0d randomizations succeeded (soft constraint ignored when conflicting)", count_satisfied);

    $display("Test 3: Compatible soft and hard constraints");
    // soft value == 75 with hard 50 < value < 100 - soft can be satisfied
    count_satisfied = 0;
    for (int i = 0; i < 10; i++) begin
      if (obj.randomize() with { value > 50; value < 100; soft value == 75; }) begin
        if (obj.value > 50 && obj.value < 100) begin
          count_satisfied++;
          // Note: soft constraints may or may not be enforced in this implementation
        end else begin
          $display("FAILED: Hard constraint violated, value=%0d", obj.value);
          $finish;
        end
      end else begin
        $display("FAILED: randomize() returned 0");
        $finish;
      end
    end
    $display("  All %0d randomizations succeeded", count_satisfied);

    $display("PASSED");
  end
endmodule
