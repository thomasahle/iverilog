// Test bit-select on struct members with variable index
// Pattern: struct.member[variable_idx]

module test;
  typedef struct packed {
    logic [7:0] data;
    logic [3:0] addr;
  } packet_t;

  initial begin
    packet_t pkt;
    int idx;
    logic bit_val;

    pkt.data = 8'b10101010;
    pkt.addr = 4'b1100;

    // Test variable bit-select on data member
    for (idx = 0; idx < 8; idx++) begin
      bit_val = pkt.data[idx];
      if (bit_val != ((idx % 2 == 1) ? 1'b1 : 1'b0)) begin
        $display("FAILED: pkt.data[%0d] = %b, expected %b", idx, bit_val, (idx % 2 == 1));
        $finish;
      end
    end

    // Test variable bit-select on addr member
    for (idx = 0; idx < 4; idx++) begin
      bit_val = pkt.addr[idx];
      if ((idx < 2 && bit_val != 1'b0) || (idx >= 2 && bit_val != 1'b1)) begin
        $display("FAILED: pkt.addr[%0d] = %b", idx, bit_val);
        $finish;
      end
    end

    $display("PASSED");
  end
endmodule
