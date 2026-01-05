// Test property overlapping implication |->
// a |-> b means "if a then b" which is logically equivalent to !a || b
module test;
  reg clk;
  reg a, b;
  int pass_count = 0;
  int fail_count = 0;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test overlapping implication: a |-> b means "if a then b"
  // Pass action when property holds, fail action when it doesn't
  always @(posedge clk) begin
    assert property (a |-> b)
      pass_count++;
    else
      fail_count++;
  end

  initial begin
    // Initialize
    a = 0; b = 0;

    // Test 1: a=0, b=0 -> property should pass (a is false, so implication is vacuously true)
    @(posedge clk);
    @(negedge clk);

    // Test 2: a=0, b=1 -> property should pass (a is false)
    a = 0; b = 1;
    @(posedge clk);
    @(negedge clk);

    // Test 3: a=1, b=1 -> property should pass (a is true and b is true)
    a = 1; b = 1;
    @(posedge clk);
    @(negedge clk);

    // Test 4: a=1, b=0 -> property should FAIL (a is true but b is false)
    a = 1; b = 0;
    @(posedge clk);
    @(negedge clk);

    // Verify results
    if (pass_count == 3 && fail_count == 1) begin
      $display("PASSED");
    end else begin
      $display("FAILED: Expected pass=3, fail=1, got pass=%0d, fail=%0d", pass_count, fail_count);
    end

    $finish;
  end
endmodule
