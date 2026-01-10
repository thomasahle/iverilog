// Test foreach constraint unrolling
// foreach(arr[i]) arr[i] constraint should be unrolled at elaboration time

module test;

class tx;
  rand bit [7:0] data[4];

  // Each element must be in range [10, 200]
  constraint data_range {
    foreach(data[i]) {
      data[i] >= 10;
      data[i] <= 200;
    }
  }
endclass

initial begin
  tx t = new();
  int pass = 1;

  // Randomize multiple times
  repeat(5) begin
    if (!t.randomize()) begin
      $display("FAILED: randomize returned 0");
      $finish;
    end

    // Verify all elements are in range
    for (int i = 0; i < 4; i++) begin
      if (t.data[i] < 10 || t.data[i] > 200) begin
        $display("FAILED: data[%0d] = %0d is out of range [10, 200]", i, t.data[i]);
        pass = 0;
      end
    end
  end

  if (pass)
    $display("PASSED");
  $finish;
end

endmodule
