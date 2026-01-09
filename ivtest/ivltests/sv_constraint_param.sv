// Test parameter-based constraints (default parameters only)
// Note: Parameter override values in class specializations are not yet fully supported

module test;
  class tx #(int MAX_VAL = 10);
    rand bit [7:0] value;
    constraint c1 { value < MAX_VAL; }
  endclass

  initial begin
    automatic tx t = new();
    automatic int passed = 1;
    repeat(50) begin
      if (t.randomize()) begin
        if (t.value >= 10) begin
          $display("FAILED: value = %0d, expected < 10", t.value);
          passed = 0;
        end
      end else begin
        $display("Randomization FAILED");
        passed = 0;
      end
    end
    if (passed) $display("PASSED");
    else $display("FAILED");
  end
endmodule
