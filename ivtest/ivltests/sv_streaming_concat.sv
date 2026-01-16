// Test streaming concatenation operators
module test;
  logic [31:0] a, b;
  logic [7:0] byte0, byte1, byte2, byte3;
  int errors = 0;
  
  initial begin
    // Test 1: Right-stream (>>) packs left-to-right (MSB first)
    a = 32'h11223344;
    {>> 8 {byte0, byte1, byte2, byte3}} = a;
    if ({byte0, byte1, byte2, byte3} !== 32'h11223344) begin
      $display("FAILED: Right-stream unpack, expected 11223344, got %h%h%h%h",
               byte0, byte1, byte2, byte3);
      errors = errors + 1;
    end
    
    // Test 2: Left-stream (<<) packs right-to-left (LSB first)
    {<< 8 {byte0, byte1, byte2, byte3}} = a;
    if ({byte0, byte1, byte2, byte3} !== 32'h44332211) begin
      $display("FAILED: Left-stream unpack, expected 44332211, got %h%h%h%h",
               byte0, byte1, byte2, byte3);
      errors = errors + 1;
    end
    
    // Test 3: Right-stream pack
    byte0 = 8'hAA; byte1 = 8'hBB; byte2 = 8'hCC; byte3 = 8'hDD;
    b = {>> 8 {byte0, byte1, byte2, byte3}};
    if (b !== 32'hAABBCCDD) begin
      $display("FAILED: Right-stream pack, expected AABBCCDD, got %h", b);
      errors = errors + 1;
    end
    
    // Test 4: Left-stream pack
    b = {<< 8 {byte0, byte1, byte2, byte3}};
    if (b !== 32'hDDCCBBAA) begin
      $display("FAILED: Left-stream pack, expected DDCCBBAA, got %h", b);
      errors = errors + 1;
    end
    
    // Test 5: Basic streaming without slice_size
    b = {>> {8'hAB, 8'hCD, 8'hEF, 8'h12}};
    if (b !== 32'hABCDEF12) begin
      $display("FAILED: Basic right-stream, expected ABCDEF12, got %h", b);
      errors = errors + 1;
    end
    
    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
