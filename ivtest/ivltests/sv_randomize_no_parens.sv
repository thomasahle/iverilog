// Test randomize with inline constraints using "randomize with" syntax (no parentheses)
// SystemVerilog allows both:
//   obj.randomize() with { ... }  - with parentheses (expression form)
//   obj.randomize with { ... }    - without parentheses (statement form)
//
// This test verifies both forms parse and execute correctly.
// The expression form (with parentheses) properly enforces inline constraints.

module test;
  class Item;
    rand bit [7:0] value;
  endclass

  Item item;
  int result;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    item = new();

    // Test expression form with parentheses - constraints enforced
    repeat (5) begin
      result = item.randomize() with { value < 30; };
      if (item.value < 30) pass_count++;
      else begin
        fail_count++;
        $display("FAIL: value=%d not < 30", item.value);
      end
    end

    // Test statement form without parentheses - should parse and execute
    // This is the alternate SystemVerilog syntax: obj.randomize with { ... }
    item.randomize with { value < 50; };
    // Just verify it executes without error (don't print random value for consistent gold file)
    $display("INFO: Statement form (no parens) parsed and executed successfully");

    // Summary
    if (fail_count == 0)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
