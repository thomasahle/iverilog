// Test array size constraints with range
// Verifies: data.size() > min; data.size() <= max;

module test;

  class Packet;
    rand bit [7:0] data[];

    // Size must be between 3 and 8 (inclusive upper bound)
    constraint c_size {
      data.size() >= 3;
      data.size() <= 8;
    }
  endclass

  initial begin
    Packet pkt;
    int size_counts[9];  // Track sizes 0-8
    int i;

    pkt = new();

    repeat (100) begin
      if (!pkt.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      // Check size is in range
      if (pkt.data.size() < 3 || pkt.data.size() > 8) begin
        $display("FAILED: size %0d out of range [3,8]", pkt.data.size());
        $finish;
      end

      if (pkt.data.size() < 9) size_counts[pkt.data.size()]++;
    end

    // Verify sizes 0-2 not used
    for (i = 0; i < 3; i++) begin
      if (size_counts[i] != 0) begin
        $display("FAILED: size %0d should not occur", i);
        $finish;
      end
    end

    $display("PASSED");
    $finish;
  end

endmodule
