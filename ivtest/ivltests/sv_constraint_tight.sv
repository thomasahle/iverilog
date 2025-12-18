// Test constraint with very tight range (only 3 possible values)
module test;

class TightConstraint;
  rand int value;

  constraint c_tight {
    value >= 5;
    value <= 7;
  }
endclass

initial begin
  TightConstraint obj;
  int pass_count = 0;
  int fail_count = 0;
  int i;

  obj = new();

  for (i = 0; i < 20; i++) begin
    if (obj.randomize()) begin
      if (obj.value >= 5 && obj.value <= 7) begin
        pass_count++;
      end else begin
        $display("FAIL: value=%0d out of range [5,7]", obj.value);
        fail_count++;
      end
    end else begin
      $display("FAIL: randomize() returned 0");
      fail_count++;
    end
  end

  if (fail_count == 0) begin
    $display("PASSED: %0d randomizations in valid range [5,7]", pass_count);
  end else begin
    $display("FAILED: %0d failures", fail_count);
  end

  $finish;
end

endmodule
