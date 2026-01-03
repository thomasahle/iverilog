// Test local static variable in function
module test;
  function automatic int counter();
    static int count = 0;  // Should persist across calls
    count++;
    return count;
  endfunction

  int c1, c2, c3;
  int errors = 0;

  initial begin
    c1 = counter();
    c2 = counter();
    c3 = counter();

    $display("c1=%0d c2=%0d c3=%0d", c1, c2, c3);

    if (c1 != 1 || c2 != 2 || c3 != 3) begin
      $display("FAILED: expected 1,2,3 got %0d,%0d,%0d", c1, c2, c3);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
