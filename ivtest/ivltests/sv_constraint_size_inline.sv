// Test inline size() constraint in randomize() with {...}
// This tests resizing dynamic arrays via constraint expressions
module test;

class packet;
  rand bit [7:0] data[];
  rand bit [15:0] addr[];
endclass

initial begin
  packet p = new();

  // Test basic size constraint
  if (!p.randomize() with { data.size() == 3; }) begin
    $display("FAILED: randomize returned 0");
    $finish;
  end

  if (p.data.size() != 3) begin
    $display("FAILED: data.size() = %0d, expected 3", p.data.size());
    $finish;
  end

  // Test different size
  if (!p.randomize() with { data.size() == 5; }) begin
    $display("FAILED: randomize returned 0 for size 5");
    $finish;
  end

  if (p.data.size() != 5) begin
    $display("FAILED: data.size() = %0d, expected 5", p.data.size());
    $finish;
  end

  // Test multiple arrays with different sizes
  if (!p.randomize() with { data.size() == 2; addr.size() == 4; }) begin
    $display("FAILED: randomize returned 0 for multiple arrays");
    $finish;
  end

  if (p.data.size() != 2) begin
    $display("FAILED: data.size() = %0d, expected 2", p.data.size());
    $finish;
  end

  if (p.addr.size() != 4) begin
    $display("FAILED: addr.size() = %0d, expected 4", p.addr.size());
    $finish;
  end

  // Test size constraint with value 0 (empty array)
  if (!p.randomize() with { data.size() == 0; }) begin
    $display("FAILED: randomize returned 0 for size 0");
    $finish;
  end

  if (p.data.size() != 0) begin
    $display("FAILED: data.size() = %0d, expected 0", p.data.size());
    $finish;
  end

  $display("PASSED");
  $finish;
end

endmodule
