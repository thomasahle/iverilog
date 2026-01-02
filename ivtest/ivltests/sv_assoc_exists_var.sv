// Test exists() on associative array with variable key
// The key doesn't need to be a constant expression

module test;
  bit [7:0] mem [int];
  int keys[3] = '{10, 20, 30};
  int pass = 1;
  
  initial begin
    // Add some entries
    mem[10] = 8'hAA;
    mem[20] = 8'hBB;
    
    // Test exists() with variable key
    for (int i = 0; i < 3; i++) begin
      if (i < 2) begin
        if (!mem.exists(keys[i])) begin
          $display("FAILED: mem.exists(%0d) should be 1", keys[i]);
          pass = 0;
        end
      end else begin
        if (mem.exists(keys[i])) begin
          $display("FAILED: mem.exists(%0d) should be 0", keys[i]);
          pass = 0;
        end
      end
    end
    
    // Test exists() with function parameter (like AXI4 AVIP)
    if (!check_key_exists(10)) begin
      $display("FAILED: check_key_exists(10) should be 1");
      pass = 0;
    end
    if (check_key_exists(99)) begin
      $display("FAILED: check_key_exists(99) should be 0");
      pass = 0;
    end
    
    if (pass) $display("PASSED");
  end
  
  function bit check_key_exists(input int key);
    return mem.exists(key);
  endfunction
endmodule
