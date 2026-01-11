// Test foreach with != constraint (inline version)
// Note: Named constraint with foreach != on dynamic arrays doesn't work
//       Use inline constraints as workaround

class Packet;
  rand bit [7:0] data[];
endclass

module test;
  initial begin
    Packet p;
    int fail_count;

    p = new();
    fail_count = 0;

    // Use inline constraint - works correctly
    repeat(20) begin
      if (!p.randomize() with {
        data.size() == 5;
        foreach(data[i]) data[i] != 0;
      }) begin
        $display("FAILED: randomize failed");
        $finish;
      end
      for (int i = 0; i < 5; i++) begin
        if (p.data[i] == 0) begin
          $display("FAILED: data[%0d]=0, should be non-zero", i);
          fail_count++;
        end
      end
    end

    if (fail_count == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d zero values found", fail_count);
    $finish;
  end
endmodule
