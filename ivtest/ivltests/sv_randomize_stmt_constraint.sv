// Test that statement-form randomize() with inline constraints actually enforces constraints
// Both syntactic forms should enforce constraints:
//   obj.randomize() with { ... }  - with parentheses
//   obj.randomize with { ... }    - without parentheses

module test;
  class Item;
    rand bit [7:0] value;
  endclass

  Item item;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    item = new();

    // Test statement form WITH parentheses - constraints should be enforced
    repeat (10) begin
      item.randomize() with { value < 50; };
      if (item.value < 50) pass_count++;
      else begin
        fail_count++;
        $display("FAIL: statement form with parens: value=%d not < 50", item.value);
      end
    end

    // Test statement form WITHOUT parentheses - constraints should also be enforced
    repeat (10) begin
      item.randomize with { value >= 100; value < 150; };
      if (item.value >= 100 && item.value < 150) pass_count++;
      else begin
        fail_count++;
        $display("FAIL: statement form no parens: value=%d not in [100,150)", item.value);
      end
    end

    // Summary
    if (fail_count == 0)
      $display("PASSED: %0d/20 constraints enforced", pass_count);
    else
      $display("FAILED: %0d/%0d constraints failed", fail_count, pass_count + fail_count);
  end
endmodule
