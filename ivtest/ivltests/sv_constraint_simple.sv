// Test simple constraint bounds in randomize()
module test;

class SimpleConstraint;
  rand int value;

  constraint c_bounds {
    value >= 10;
    value < 100;
  }
endclass

initial begin
  SimpleConstraint obj;
  int pass_count = 0;
  int fail_count = 0;
  int i;

  obj = new();

  for (i = 0; i < 20; i++) begin
    if (obj.randomize()) begin
      if (obj.value >= 10 && obj.value < 100) begin
        pass_count++;
      end else begin
        $display("FAIL: value=%0d out of range [10,100)", obj.value);
        fail_count++;
      end
    end else begin
      $display("FAIL: randomize() returned 0");
      fail_count++;
    end
  end

  if (fail_count == 0) begin
    $display("PASSED: %0d randomizations in valid range", pass_count);
  end else begin
    $display("FAILED: %0d failures", fail_count);
  end

  $finish;
end

endmodule
