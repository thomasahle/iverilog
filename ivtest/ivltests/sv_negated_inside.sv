// Test negated inside constraint
// The constraint !(value inside {[10:20]}) should exclude values in range 10-20
class Test;
  rand bit [7:0] value;

  // Value should NOT be in range 10-20
  constraint not_in_range { !(value inside {[10:20]}); }
endclass

module test;
  Test t;
  int in_range, out_range;

  initial begin
    t = new();
    in_range = 0;
    out_range = 0;

    repeat(100) begin
      if (!t.randomize()) begin
        $display("FAIL: randomize failed");
      end else begin
        if (t.value >= 10 && t.value <= 20)
          in_range++;
        else
          out_range++;
      end
    end

    $display("Results: in_range=%0d, out_range=%0d", in_range, out_range);
    if (in_range == 0 && out_range == 100)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
