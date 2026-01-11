// Test dist constraint with unbounded range [N:$]
// Verifies: x dist { [0:5] := 80, [6:$] :/ 20 }

module test;

  class Packet;
    rand bit [3:0] value;  // 0-15

    // 80% weight for 0-5 (6 values), 20% for 6-15 (10 values)
    constraint c_dist {
      value dist { [0:5] := 80, [6:$] :/ 20 };
    }
  endclass

  initial begin
    Packet pkt;
    int low_count, high_count;

    pkt = new();
    low_count = 0;
    high_count = 0;

    repeat (300) begin
      if (!pkt.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      if (pkt.value <= 5)
        low_count++;
      else
        high_count++;
    end

    $display("Low range (0-5): %0d, High range (6-15): %0d", low_count, high_count);

    // Values should be within range
    if (low_count == 0 || high_count == 0) begin
      $display("FAILED: One range has no values");
      $finish;
    end

    // Low should be more weighted
    if (low_count < high_count) begin
      $display("FAILED: Expected more values in low range");
      $finish;
    end

    $display("Distribution looks reasonable");
    $display("PASSED");
    $finish;
  end

endmodule
