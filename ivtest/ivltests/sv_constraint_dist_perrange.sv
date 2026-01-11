// Test dist constraint with :/ (weight per range) syntax
// Verifies: x dist { [0:9] :/ 90, [10:$] :/ 10 }

module test;

  class Packet;
    rand bit [7:0] value;

    // 90% weight for 0-9, 10% weight for 10-255
    constraint c_dist {
      value dist { [0:9] :/ 90, [10:255] :/ 10 };
    }
  endclass

  initial begin
    Packet pkt;
    int low_count, high_count, i;

    pkt = new();
    low_count = 0;
    high_count = 0;

    repeat (200) begin
      if (!pkt.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      if (pkt.value <= 9)
        low_count++;
      else
        high_count++;
    end

    // With 90:10 weights, low should be significantly more than high
    // Allow some variance but expect at least 60% in low range
    if (low_count < 100) begin
      $display("FAILED: Expected more values in low range (got %0d)", low_count);
      $finish;
    end

    $display("PASSED");
    $finish;
  end

endmodule
