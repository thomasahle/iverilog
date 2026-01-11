// Test foreach with bounds constraints (WORKS)
// Note: foreach with element equality to external array doesn't work yet

module test;
  class Transaction;
    rand bit [7:0] data[];
  endclass
  
  Transaction t;
  
  initial begin
    t = new();
    
    // Randomize with foreach bounds constraints (this works)
    if (!t.randomize() with {
      data.size() == 5;
      foreach(data[i]) { data[i] >= 8'h10; data[i] <= 8'h20; }
    }) begin
      $display("FAILED: randomize failed");
      $finish;
    end
    
    // Verify all elements are in range [0x10, 0x20]
    foreach (t.data[i]) begin
      if (t.data[i] < 8'h10 || t.data[i] > 8'h20) begin
        $display("FAILED: data[%0d]=%h out of range [10,20]", i, t.data[i]);
        $finish;
      end
    end
    
    $display("PASSED");
    $finish;
  end
endmodule
