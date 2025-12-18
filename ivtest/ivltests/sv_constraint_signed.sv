// Test constraint bounds with signed (negative) values
module test;

class SignedConstraint;
  rand int value;  // signed 32-bit

  constraint c_negative {
    value >= -50;
    value < 0;
  }
endclass

initial begin
  SignedConstraint obj;
  int pass_count = 0;
  int fail_count = 0;
  int i;

  obj = new();

  for (i = 0; i < 20; i++) begin
    if (obj.randomize()) begin
      if (obj.value >= -50 && obj.value < 0) begin
        pass_count++;
      end else begin
        $display("FAIL: value=%0d out of range [-50,0)", obj.value);
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
