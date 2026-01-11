// Test basic foreach constraint on static arrays
// Verifies: foreach(arr[i]) { arr[i] >= 10; arr[i] <= 100; }

module test;

  class Packet;
    rand bit [7:0] data[4];

    // All elements between 10 and 100
    constraint c_range {
      foreach(data[i]) {
        data[i] >= 10;
        data[i] <= 100;
      }
    }
  endclass

  initial begin
    Packet pkt;
    int i;
    int pass_count;

    pkt = new();
    pass_count = 0;

    repeat (20) begin
      if (!pkt.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      // Check all elements are in range
      for (i = 0; i < 4; i++) begin
        if (pkt.data[i] < 10 || pkt.data[i] > 100) begin
          $display("FAILED: data[%0d]=%0d out of range [10,100]", i, pkt.data[i]);
          $finish;
        end
      end

      pass_count++;
    end

    $display("All %0d randomizations passed", pass_count);
    $display("PASSED");
    $finish;
  end

endmodule
