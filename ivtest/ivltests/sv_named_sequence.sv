// Test for named sequence declarations
// Named sequences can be used in properties and assertions

module test;
  reg clk, rst, data, ready, valid;

  // Simple named sequence (non-parameterized)
  sequence seq_data_stable;
    @(posedge clk) $stable(data);
  endsequence

  // Parameterized sequence
  sequence seq_signal_true(logic sig);
    @(posedge clk) sig;
  endsequence

  // Sequence used in property
  property p_data_stable_when_ready;
    @(posedge clk) ready |-> seq_data_stable;
  endproperty

  // Use sequences in assertions
  assert property (p_data_stable_when_ready);
  assert property (@(posedge clk) valid |-> seq_signal_true(data));

  // Test stimulus
  initial begin
    clk = 0;
    rst = 0;
    data = 0;
    ready = 0;
    valid = 0;

    #5 rst = 1;

    // Test sequence with data stable during ready
    #10 ready = 1; data = 1;
    #10 ready = 0;

    // Test parameterized sequence
    #10 valid = 1; data = 1;
    #10 valid = 0;

    #10 $display("PASSED");
    $finish;
  end

  always #5 clk = ~clk;
endmodule
