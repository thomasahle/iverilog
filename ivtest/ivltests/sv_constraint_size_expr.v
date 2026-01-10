// Test size constraint with property expression: data.size() == len + 1
module test;

class packet;
  rand bit [7:0] data[];
  rand bit [3:0] len;

  constraint size_c { data.size() == len + 1; }
  constraint len_c { len >= 2; len <= 5; }
endclass

initial begin
  packet p = new();

  for (int i = 0; i < 5; i++) begin
    if (!p.randomize()) begin
      $display("FAILED: randomize returned 0");
      $finish;
    end

    // Verify the size constraint is satisfied
    if (p.data.size() != p.len + 1) begin
      $display("FAILED: data.size() = %0d, expected %0d (len=%0d)",
               p.data.size(), p.len + 1, p.len);
      $finish;
    end

    // Verify len is within range
    if (p.len < 2 || p.len > 5) begin
      $display("FAILED: len = %0d, out of range [2:5]", p.len);
      $finish;
    end

    // Passed - randomization and constraint both satisfied
  end

  $display("PASSED");
  $finish;
end

endmodule
