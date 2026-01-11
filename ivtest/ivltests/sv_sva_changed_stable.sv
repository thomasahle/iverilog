// Test SVA $changed and $stable sampled value functions
module test;
  logic clk = 0;
  logic data = 0;
  int changed_count = 0;
  int stable_count = 0;
  
  always #5 clk = ~clk;
  
  // Property: $changed detects value change
  property data_changed;
    @(posedge clk) $changed(data) |-> 1;
  endproperty
  
  // Property: $stable detects no change  
  property data_stable;
    @(posedge clk) $stable(data) |-> 1;
  endproperty
  
  // Cover changed
  cover property (data_changed) changed_count++;
  
  // Cover stable
  cover property (data_stable) stable_count++;
  
  initial begin
    // Initial stable period
    #25;  // Several stable cycles
    
    // Toggle data
    data = 1;
    #10;
    data = 0;
    #10;
    data = 1;
    #20;  // Stable period
    
    #10;
    $display("Changed count: %0d, Stable count: %0d", changed_count, stable_count);
    
    // Should have both changes and stable periods
    if (changed_count >= 2 && stable_count >= 2)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
