// Test randcase - weighted random case statement
module test;
  int result;
  int i;
  int got_any;
  
  initial begin
    // Simple randcase - verify syntax compiles and executes
    result = 0;
    randcase
      1: result = 1;
      1: result = 2;
      1: result = 3;
    endcase
    
    // Result should be 1, 2, or 3
    if (result >= 1 && result <= 3)
      $display("PASSED: randcase syntax works");
    else
      $display("FAILED: randcase returned invalid result %0d", result);
    
    // Run multiple times and verify at least some paths are taken
    got_any = 0;
    for (i = 0; i < 50; i++) begin
      randcase
        1: got_any = got_any | 1;
        1: got_any = got_any | 2;
        1: got_any = got_any | 4;
      endcase
    end
    
    if (got_any != 0)
      $display("PASSED: randcase executes branches");
    else
      $display("FAILED: no branches executed");
  end
endmodule
