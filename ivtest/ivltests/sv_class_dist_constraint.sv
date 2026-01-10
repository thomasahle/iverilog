// Test weighted dist constraints in class constraint blocks
// The constraint `x dist { 1 := 9, 100 := 1 }` should produce
// value 1 about 90% of the time and value 100 about 10% of the time.

class tx;
  rand bit [7:0] x;

  constraint x_c {
    x dist { 1 := 9, 100 := 1 };
  }
endclass

module test;
  initial begin
    tx t;
    int ones, hundreds, others;
    int i;

    t = new();
    ones = 0;
    hundreds = 0;
    others = 0;

    for (i = 0; i < 1000; i = i + 1) begin
      if (!t.randomize()) begin
        $display("FAILED - randomize failed");
        $finish;
      end

      if (t.x == 1) ones = ones + 1;
      else if (t.x == 100) hundreds = hundreds + 1;
      else others = others + 1;
    end

    $display("ones=%0d hundreds=%0d others=%0d", ones, hundreds, others);

    // With 9:1 weighting, expect ~90% ones and ~10% hundreds
    // Allow some margin for randomness: ones should be at least 5x hundreds
    if (ones > hundreds * 5 && others == 0)
      $display("PASSED");
    else
      $display("FAILED - expected weighted distribution");
  end
endmodule
