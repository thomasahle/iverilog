// Test cover property statement support
// cover property: execute pass action when property is true
module test;
  logic clk = 0;
  logic [1:0] state = 0;
  int cover_count = 0;

  // Cover property - checks every clock edge
  always @(posedge clk) begin
    // Manual check to verify clocking works
    if (state == 2'b00) begin
      $display("Manual check: IDLE state at time %0t", $time);
    end
  end

  // Simple cover property with clocking event
  cover property (@(posedge clk) state == 2'b00)
    $display("Cover property hit: IDLE at time %0t, count=%0d", $time, cover_count++);

  // Cover property for active
  cover property (@(posedge clk) state == 2'b01)
    $display("Cover property hit: ACTIVE at time %0t", $time);

  initial begin
    state = 2'b00;
    $display("Initial state = IDLE");

    // Generate clock
    repeat (4) begin
      #10 clk = 1;
      #10 clk = 0;
    end

    state = 2'b01;
    $display("State changed to ACTIVE");
    repeat (2) begin
      #10 clk = 1;
      #10 clk = 0;
    end

    $display("Test completed, cover_count=%0d", cover_count);
    if (cover_count >= 1) begin
      $display("PASSED");
    end else begin
      $display("FAILED: Expected at least 1 coverage hit, got %0d", cover_count);
    end
    $finish;
  end
endmodule
