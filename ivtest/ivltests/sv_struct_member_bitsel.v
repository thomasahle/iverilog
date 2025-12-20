// Test constant bit-select assignment on struct members (l-value)
// Pattern: struct.member[bit_idx] = value

module test;
  typedef struct packed {
    logic [7:0] data;
    logic [3:0] ctrl;
  } packet_t;

  initial begin
    packet_t pkt;

    // Initialize
    pkt.data = 8'h00;
    pkt.ctrl = 4'h0;

    // Set individual bits in data
    pkt.data[0] = 1'b1;
    pkt.data[2] = 1'b1;
    pkt.data[4] = 1'b1;
    pkt.data[6] = 1'b1;

    if (pkt.data != 8'b01010101) begin
      $display("FAILED: pkt.data = %b, expected 01010101", pkt.data);
      $finish;
    end

    // Set individual bits in ctrl
    pkt.ctrl[1] = 1'b1;
    pkt.ctrl[3] = 1'b1;

    if (pkt.ctrl != 4'b1010) begin
      $display("FAILED: pkt.ctrl = %b, expected 1010", pkt.ctrl);
      $finish;
    end

    $display("PASSED");
  end
endmodule
