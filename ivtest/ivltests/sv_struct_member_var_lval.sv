// Test variable bit-select on struct members as l-value
// This tests assigning to struct.member[i] where i is a variable

module test;
  typedef struct packed {
    bit [7:0] data;
    bit [3:0] pstrb;
  } packet_t;

  packet_t pkt;
  int errors;

  initial begin
    errors = 0;
    pkt = '0;

    // Test variable bit-select on struct member (write)
    for (int i = 0; i < 4; i++) begin
      pkt.data[i] = 1'b1;  // Set bits 0-3 to 1
    end

    if (pkt.data !== 8'h0F) begin
      $display("FAILED test 1: expected data=0x0F, got 0x%02h", pkt.data);
      errors++;
    end

    // Test setting bits 4-7
    for (int i = 4; i < 8; i++) begin
      pkt.data[i] = 1'b1;
    end

    if (pkt.data !== 8'hFF) begin
      $display("FAILED test 2: expected data=0xFF, got 0x%02h", pkt.data);
      errors++;
    end

    // Test clearing bits using variable index
    pkt.data = 8'hFF;
    for (int i = 0; i < 8; i += 2) begin
      pkt.data[i] = 1'b0;  // Clear even bits
    end

    if (pkt.data !== 8'hAA) begin
      $display("FAILED test 3: expected data=0xAA, got 0x%02h", pkt.data);
      errors++;
    end

    // Test on different member
    pkt.pstrb = 4'b0000;
    for (int i = 0; i < 2; i++) begin
      pkt.pstrb[i] = 1'b1;
    end

    if (pkt.pstrb !== 4'b0011) begin
      $display("FAILED test 4: expected pstrb=0x3, got 0x%01h", pkt.pstrb);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
