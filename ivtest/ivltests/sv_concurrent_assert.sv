// Test basic concurrent assertion support
// Checks that simple property expression is executed

module test;
  reg clk;
  reg data_valid;
  reg data_ready;
  int pass_count;
  int fail_count;

  // Generate clock
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test concurrent assertion - simple case (no sequences)
  // When inside an always @(posedge clk), we don't need another clock event
  always @(posedge clk) begin
    assert property (data_valid && data_ready)
      pass_count++;
    else
      fail_count++;
  end

  initial begin
    pass_count = 0;
    fail_count = 0;
    data_valid = 0;
    data_ready = 0;

    // First edge: both low -> fail expected
    @(posedge clk);
    #1; // Small delay to let always block execute

    // Second edge: data_valid high, data_ready low -> fail expected
    data_valid = 1;
    @(posedge clk);
    #1;

    // Third edge: both high -> pass expected
    data_ready = 1;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;

    $display("Pass count: %0d, Fail count: %0d", pass_count, fail_count);

    // We expect 3 passes (when both high) and 2 fails (initial conditions)
    if (pass_count >= 2 && fail_count >= 2)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
