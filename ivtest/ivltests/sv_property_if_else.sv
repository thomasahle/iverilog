// Test property if-then-else
// if(cond) prop1 else prop2: check prop1 when cond is true, prop2 when false
module test;
  reg clk;
  reg sel, a, b;
  int pass_count = 0;
  int fail_count = 0;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test if-then-else property: if(sel) a else b
  // When sel=1, check a is true; when sel=0, check b is true
  always @(posedge clk) begin
    assert property (if(sel) a else b)
      pass_count++;
    else
      fail_count++;
  end

  initial begin
    // Initialize
    sel = 0; a = 0; b = 0;

    // Test 1: sel=0, b=1 -> should pass (checking b when sel=0)
    sel = 0; a = 0; b = 1;
    @(posedge clk);
    @(negedge clk);

    // Test 2: sel=0, b=0 -> should FAIL (b is false when sel=0)
    sel = 0; a = 1; b = 0;
    @(posedge clk);
    @(negedge clk);

    // Test 3: sel=1, a=1 -> should pass (checking a when sel=1)
    sel = 1; a = 1; b = 0;
    @(posedge clk);
    @(negedge clk);

    // Test 4: sel=1, a=0 -> should FAIL (a is false when sel=1)
    sel = 1; a = 0; b = 1;
    @(posedge clk);
    @(negedge clk);

    // Verify results: expect 2 passes, 2 fails
    if (pass_count == 2 && fail_count == 2) begin
      $display("PASSED");
    end else begin
      $display("FAILED: Expected pass=2, fail=2, got pass=%0d, fail=%0d", pass_count, fail_count);
    end

    $finish;
  end
endmodule
