// Test dist weight semantics: := (per-value) vs :/ (per-range)
// := means the weight is applied to each value individually
// :/ means the weight is divided among all values in the range

module test;
  class tx;
    rand bit [7:0] val;

    // := gives each value weight 10, so values 1-3 each have weight 10
    // Total weight = 10 + 10 + 10 + 100 = 130
    // P(val==1) = P(val==2) = P(val==3) = 10/130 = 7.7%
    // P(val==100) = 100/130 = 77%
    constraint c_per_value {
      val dist { [1:3] := 10, 100 := 100 };
    }
  endclass

  class tx2;
    rand bit [7:0] val;

    // :/ gives the range total weight 30, divided among 3 values
    // Each of values 1-3 gets weight 10 (30/3)
    // Total weight = 30 + 100 = 130
    // Same distribution as above
    constraint c_per_range {
      val dist { [1:3] :/ 30, 100 := 100 };
    }
  endclass

  int count_low, count_high;
  int passed;

  initial begin
    tx t1;
    tx2 t2;

    // Test := semantics
    t1 = new;
    count_low = 0;
    count_high = 0;

    repeat (1000) begin
      void'(t1.randomize());
      if (t1.val >= 1 && t1.val <= 3) count_low++;
      else if (t1.val == 100) count_high++;
    end

    // With weights 30:100, expect ~23% low and ~77% high
    // Allow 10-40% for low values, 50-95% for high value
    passed = 1;
    if (count_low < 100 || count_low > 400) begin
      $display("FAILED: := semantics - low count %0d out of expected 100-400", count_low);
      passed = 0;
    end
    if (count_high < 500 || count_high > 950) begin
      $display("FAILED: := semantics - high count %0d out of expected 500-950", count_high);
      passed = 0;
    end

    // Test :/ semantics - should produce similar distribution
    t2 = new;
    count_low = 0;
    count_high = 0;

    repeat (1000) begin
      void'(t2.randomize());
      if (t2.val >= 1 && t2.val <= 3) count_low++;
      else if (t2.val == 100) count_high++;
    end

    if (count_low < 100 || count_low > 400) begin
      $display("FAILED: :/ semantics - low count %0d out of expected 100-400", count_low);
      passed = 0;
    end
    if (count_high < 500 || count_high > 950) begin
      $display("FAILED: :/ semantics - high count %0d out of expected 500-950", count_high);
      passed = 0;
    end

    if (passed)
      $display("PASSED");
  end
endmodule
