// Test named struct aggregate assignment patterns
// SystemVerilog LRM 10.9.2 structure assignment patterns

module test;
  typedef struct packed {
    logic [7:0] alpha;
    logic [7:0] beta;
    logic [7:0] gamma;
  } struct_t;
  
  struct_t s1, s2;
  int errors = 0;
  
  initial begin
    // Test 1: Named pattern in declaration order
    s1 = '{alpha: 8'd10, beta: 8'd20, gamma: 8'd30};
    if (s1.alpha !== 10 || s1.beta !== 20 || s1.gamma !== 30) begin
      $display("FAILED: Test 1 - basic named pattern");
      errors++;
    end
    
    // Test 2: Named pattern out of order  
    s2 = '{gamma: 8'd100, alpha: 8'd50, beta: 8'd75};
    if (s2.alpha !== 50 || s2.beta !== 75 || s2.gamma !== 100) begin
      $display("FAILED: Test 2 - out of order named pattern");
      errors++;
    end
    
    // Test 3: Use expressions in values
    s1 = '{alpha: s2.gamma, beta: s2.alpha + 1, gamma: 8'd0};
    if (s1.alpha !== 100 || s1.beta !== 51 || s1.gamma !== 0) begin
      $display("FAILED: Test 3 - expressions in values");
      errors++;
    end
    
    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
