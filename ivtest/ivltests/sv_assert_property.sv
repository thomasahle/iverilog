// Test assert property statement support at module level
// Note: Implication (|->) is not yet supported, only simple expressions
module test;
  logic clk = 0;
  logic rst_n = 0;
  logic valid = 0;
  logic ready = 0;
  int pass_count = 0;
  int fail_count = 0;

  // Simple assert property (expression only, no implication)
  assert property (@(posedge clk) disable iff (!rst_n) ready || !valid)
    pass_count++;
  else begin
    fail_count++;
    $display("Assert failed at time %0t: valid=%b, ready=%b", $time, valid, ready);
  end

  initial begin
    rst_n = 0;
    valid = 0;
    ready = 0;

    // Generate clock while reset is low
    repeat (2) begin
      #10 clk = 1; #10 clk = 0;
    end

    // Enable reset
    rst_n = 1;
    $display("Reset released");

    // Test 1: valid=0, ready=0 (should pass: !valid is true)
    valid = 0; ready = 0;
    #10 clk = 1; #10 clk = 0;
    $display("After valid=0, ready=0: pass=%0d, fail=%0d", pass_count, fail_count);

    // Test 2: valid=1, ready=1 (should pass: ready is true)
    valid = 1; ready = 1;
    #10 clk = 1; #10 clk = 0;
    $display("After valid=1, ready=1: pass=%0d, fail=%0d", pass_count, fail_count);

    // Test 3: valid=1, ready=0 (should fail: neither ready nor !valid)
    valid = 1; ready = 0;
    #10 clk = 1; #10 clk = 0;
    $display("After valid=1, ready=0: pass=%0d, fail=%0d", pass_count, fail_count);

    // Test 4: valid=0, ready=0 (should pass)
    valid = 0; ready = 0;
    #10 clk = 1; #10 clk = 0;
    $display("After valid=0, ready=0: pass=%0d, fail=%0d", pass_count, fail_count);

    $display("Final: pass_count=%0d, fail_count=%0d", pass_count, fail_count);
    if (pass_count >= 3 && fail_count >= 1) begin
      $display("PASSED");
    end else begin
      $display("FAILED: Expected at least 3 passes and 1 fail");
    end
    $finish;
  end
endmodule
