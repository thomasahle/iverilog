// Test size constraint with property division: data.size() == total / divisor
// This pattern is used in I2S AVIP and other testbenches
module test;

class packet;
  rand bit [7:0] data[];
  rand bit [7:0] total;
  
  // Size constraint with division: size = total / 4
  constraint size_c { data.size() == total / 4; }
  constraint total_c { total >= 8; total <= 20; }
endclass

initial begin
  packet p = new();
  int pass = 1;
  
  for (int i = 0; i < 5; i++) begin
    if (!p.randomize()) begin
      $display("FAILED: randomize returned 0");
      $finish;
    end
    
    // Verify size constraint
    if (p.data.size() != p.total / 4) begin
      $display("FAILED: data.size() = %0d, expected %0d (total=%0d)",
               p.data.size(), p.total / 4, p.total);
      pass = 0;
    end
    
    // Verify total is in range
    if (p.total < 8 || p.total > 20) begin
      $display("FAILED: total = %0d, out of range [8:20]", p.total);
      pass = 0;
    end
  end
  
  if (pass)
    $display("PASSED");
  $finish;
end

endmodule
