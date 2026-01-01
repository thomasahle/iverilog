// Test bulk struct array member copy, especially after loop initialization
// This tests the flags[4] fix for struct member store
module test;
  typedef struct {
    logic [7:0] header;
    logic [31:0] data[4];
    logic [7:0] footer;
  } packet_t;
  
  packet_t src, dst;
  int i;
  int pass_count = 0;
  
  initial begin
    // Test 1: Loop initialization + bulk copy (the bug case)
    for (i = 0; i < 4; i++)
      src.data[i] = 32'h10000000 + i * 32'h100;
    
    dst.data = src.data;
    
    if (dst.data[0] == 32'h10000000 && dst.data[1] == 32'h10000100 &&
        dst.data[2] == 32'h10000200 && dst.data[3] == 32'h10000300) begin
      $display("PASSED: Loop init + bulk copy");
      pass_count++;
    end else begin
      $display("FAILED: Loop init + bulk copy");
      $display("  dst.data[0] = %h (expected 10000000)", dst.data[0]);
      $display("  dst.data[1] = %h (expected 10000100)", dst.data[1]);
    end
    
    // Test 2: Direct init + bulk copy (should still work)
    src.data[0] = 32'hDEAD0000;
    src.data[1] = 32'hDEAD0001;
    src.data[2] = 32'hDEAD0002;
    src.data[3] = 32'hDEAD0003;
    
    dst.data = src.data;
    
    if (dst.data[0] == 32'hDEAD0000 && dst.data[3] == 32'hDEAD0003) begin
      $display("PASSED: Direct init + bulk copy");
      pass_count++;
    end else begin
      $display("FAILED: Direct init + bulk copy");
    end
    
    // Test 3: Chain copy after loop
    for (i = 0; i < 4; i++)
      src.data[i] = 32'hBEEF0000 + i;
    
    dst.data = src.data;
    
    // Access individual elements after bulk copy
    if (dst.data[2] == 32'hBEEF0002) begin
      $display("PASSED: Indexed access after bulk copy");
      pass_count++;
    end else begin
      $display("FAILED: Indexed access after bulk copy");
    end
    
    if (pass_count == 3)
      $display("All tests passed");
    else
      $display("Some tests FAILED");
    
    $finish;
  end
endmodule
