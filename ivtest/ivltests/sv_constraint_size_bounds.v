// Test size constraint bounds (>, <, >=, <=)
module test;

class packet;
  rand bit [7:0] data[];

  // Size must be > 0 and <= 5
  constraint size_c { data.size() > 0; data.size() <= 5; }
endclass

class packet2;
  rand bit [7:0] data[];

  // Size must be >= 2 and < 8
  constraint size_c { data.size() >= 2; data.size() < 8; }
endclass

initial begin
  packet p = new();
  packet2 p2 = new();
  int pass = 1;

  // Test packet: size in [1, 5]
  for (int i = 0; i < 10; i++) begin
    if (!p.randomize()) begin
      $display("FAILED: packet.randomize() returned 0");
      $finish;
    end

    if (p.data.size() == 0 || p.data.size() > 5) begin
      $display("FAILED: packet data.size() = %0d, expected [1:5]", p.data.size());
      pass = 0;
    end
  end

  // Test packet2: size in [2, 7]
  for (int i = 0; i < 10; i++) begin
    if (!p2.randomize()) begin
      $display("FAILED: packet2.randomize() returned 0");
      $finish;
    end

    if (p2.data.size() < 2 || p2.data.size() >= 8) begin
      $display("FAILED: packet2 data.size() = %0d, expected [2:7]", p2.data.size());
      pass = 0;
    end
  end

  if (pass)
    $display("PASSED");
  $finish;
end

endmodule
