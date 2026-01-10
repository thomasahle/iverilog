// Test weighted dist constraints with ranges in class constraint blocks
// The constraint `x dist { [0:50] := 9, [100:200] := 1 }` should produce
// values in [0:50] about 9x more frequently than [100:200] per-value basis.
// With 51 values at weight 9 and 101 values at weight 1:
//   Total weight = 51*9 + 101*1 = 459 + 101 = 560
//   Expected ratio: ~4.5:1

class tx;
  rand bit [7:0] x;

  constraint x_c {
    x dist { [0:50] := 9, [100:200] := 1 };
  }
endclass

module test;
  initial begin
    tx t;
    int low, high, other;
    int i;

    t = new();
    low = 0;
    high = 0;
    other = 0;

    for (i = 0; i < 1000; i = i + 1) begin
      if (!t.randomize()) begin
        $display("FAILED - randomize failed");
        $finish;
      end

      if (t.x <= 50) low = low + 1;
      else if (t.x >= 100 && t.x <= 200) high = high + 1;
      else other = other + 1;
    end

    $display("low(0-50)=%0d high(100-200)=%0d other=%0d", low, high, other);

    // With per-value weighting, expect ~4.5:1 ratio (allow margin for variance)
    // Low should be at least 3x high, and no values outside the ranges
    if (low > high * 3 && other == 0)
      $display("PASSED");
    else
      $display("FAILED - expected weighted distribution");
  end
endmodule
