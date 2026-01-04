// Test $psprintf - UVM alias for $sformatf
module test;
  string s;
  int a = 42;
  real r = 3.14;
  
  initial begin
    // Basic integer formatting
    s = $psprintf("Value: %0d", a);
    if (s == "Value: 42")
      $display("PASSED: basic integer");
    else
      $display("FAILED: basic integer - got '%s'", s);
    
    // Multiple arguments
    s = $psprintf("Int: %0d, Real: %.2f", a, r);
    if (s == "Int: 42, Real: 3.14")
      $display("PASSED: multiple args");
    else
      $display("FAILED: multiple args - got '%s'", s);
    
    // Hex formatting
    s = $psprintf("Hex: 0x%h", 255);
    if (s == "Hex: 0x000000ff")
      $display("PASSED: hex format");
    else
      $display("FAILED: hex format - got '%s'", s);
      
    $display("All tests complete");
  end
endmodule
