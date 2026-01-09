// Test $size() in constraint expressions
module test;
  class tx;
    rand bit [7:0] idx;
    bit [15:0] data [8];  // Array of 8 elements

    // Constraint: idx must be valid array index
    constraint c1 { idx < $size(data); }
  endclass

  initial begin
    automatic tx t = new();
    automatic int passed = 1;

    $display("Testing: idx < $size(data) where data is [8] element array");
    $display("Valid indices: 0-7");
    $display("");

    repeat(20) begin
      if (t.randomize()) begin
        if (t.idx >= 8) begin
          $display("FAILED: idx = %0d, expected < 8", t.idx);
          passed = 0;
        end
      end else begin
        $display("Randomization FAILED");
        passed = 0;
      end
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
