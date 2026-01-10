// Test foreach in inline constraint block
// foreach(arr[i]) { arr[i] >= 10; arr[i] <= 100; }
// should constrain all array elements to [10, 100]

module test;

class packet;
  rand bit [7:0] data[];
endclass

initial begin
  packet p = new();

  // Test 1: Inline constraint with foreach - all elements in range [10, 100]
  if (!p.randomize() with {
    data.size() == 5;
    foreach(data[i]) {
      data[i] >= 10;
      data[i] <= 100;
    }
  }) begin
    $display("FAILED: randomize returned 0");
    $finish;
  end

  // Check results
  if (p.data.size() != 5) begin
    $display("FAILED: wrong size %0d", p.data.size());
    $finish;
  end

  for (int i = 0; i < 5; i++) begin
    if (p.data[i] < 10 || p.data[i] > 100) begin
      $display("FAILED: data[%0d]=%0d, expected [10:100]", i, p.data[i]);
      $finish;
    end
  end

  // Test 2: Different bounds
  if (!p.randomize() with {
    data.size() == 3;
    foreach(data[i]) {
      data[i] >= 50;
      data[i] <= 60;
    }
  }) begin
    $display("FAILED: second randomize returned 0");
    $finish;
  end

  if (p.data.size() != 3) begin
    $display("FAILED: second wrong size %0d", p.data.size());
    $finish;
  end

  for (int i = 0; i < 3; i++) begin
    if (p.data[i] < 50 || p.data[i] > 60) begin
      $display("FAILED: data[%0d]=%0d, expected [50:60]", i, p.data[i]);
      $finish;
    end
  end

  $display("PASSED");
  $finish;
end

endmodule
