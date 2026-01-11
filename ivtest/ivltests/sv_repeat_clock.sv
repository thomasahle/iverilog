// Test repeat with clock edge
// Based on UART/JTAG AVIP pattern: repeat(N) @(posedge clk)
//
// Tests:
// - repeat(N) @(posedge clk) waits for exactly N edges
// - repeat with variable count
// - repeat(0) is a no-op

module test;
  logic clk = 0;
  int cycle_count = 0;
  int pass = 1;

  always #5 clk = ~clk;

  // Count clock cycles (with small delay to avoid race with initial block)
  always @(posedge clk) #1 cycle_count++;

  initial begin
    int start_count;
    int n;

    // Wait for a few cycles to stabilize
    repeat(3) @(posedge clk);
    #2;
    start_count = cycle_count;

    // Test 1: repeat(5) waits for exactly 5 edges
    repeat(5) @(posedge clk);
    #2;
    if (cycle_count - start_count != 5) begin
      $display("FAIL: repeat(5) expected 5 cycles, got %0d", cycle_count - start_count);
      pass = 0;
    end

    // Test 2: repeat with variable count
    start_count = cycle_count;
    n = 3;
    repeat(n) @(posedge clk);
    #2;
    if (cycle_count - start_count != 3) begin
      $display("FAIL: repeat(n=3) expected 3 cycles, got %0d", cycle_count - start_count);
      pass = 0;
    end

    // Test 3: repeat(1) is a single wait
    start_count = cycle_count;
    repeat(1) @(posedge clk);
    #2;
    if (cycle_count - start_count != 1) begin
      $display("FAIL: repeat(1) expected 1 cycle, got %0d", cycle_count - start_count);
      pass = 0;
    end

    // Test 4: repeat(0) should be a no-op
    start_count = cycle_count;
    repeat(0) @(posedge clk);
    #2;
    if (cycle_count - start_count != 0) begin
      $display("FAIL: repeat(0) expected 0 cycles, got %0d", cycle_count - start_count);
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
