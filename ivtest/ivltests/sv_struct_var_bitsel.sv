// Test variable bit-select on struct members: struct.member[i]
// This tests the fix for accessing individual bits of a packed struct
// member using a variable index.

module test;
  typedef struct packed {
    bit [7:0] data;
    bit [3:0] pstrb;
  } packet_t;

  packet_t pkt;
  int count;

  initial begin
    pkt.data = 8'hA5;  // 10100101
    pkt.pstrb = 4'b1010;
    count = 0;

    // Test variable bit-select on struct member
    for (int i = 0; i < 4; i++) begin
      if (pkt.pstrb[i] == 1) begin
        count++;
      end
    end

    if (count == 2) begin
      $display("PASSED: variable bit-select on struct works (count=%0d)", count);
    end else begin
      $display("FAILED: expected count=2, got %0d", count);
    end

    $finish;
  end
endmodule
