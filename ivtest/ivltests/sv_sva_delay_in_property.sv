// Test ##N delay at start of property (without implication)
// Pattern from protocol AVIPs: if(cond) ##N expr

module test;
  logic clk = 0;
  logic [1:0] mode;
  logic [7:0] data;
  int pass_count = 0;

  always #5 clk = ~clk;

  // Test property with ##N delay in if-then
  // This is a common pattern in protocol AVIPs (e.g., UART)
  property p_delay_check;
    @(posedge clk)
    if (mode == 2'b01) ##4 data == 8'hAA;
  endproperty

  // Simple ##N delay at property start
  property p_simple_delay;
    @(posedge clk)
    ##2 data != 0;
  endproperty

  assert property(p_delay_check) pass_count++;
  assert property(p_simple_delay) pass_count++;

  initial begin
    mode = 0;
    data = 8'h00;

    // Cycle 1
    @(posedge clk);
    #1;

    // Cycle 2 - set data for p_simple_delay
    mode = 2'b01;
    data = 8'hAA;
    @(posedge clk);
    #1;

    // Cycle 3
    @(posedge clk);
    #1;

    // Cycle 4
    @(posedge clk);
    #1;

    if (pass_count > 0) begin
      $display("PASSED: ##N delay in property if-then works");
    end else begin
      $display("FAILED: No assertion passes recorded");
    end
    $finish;
  end
endmodule
