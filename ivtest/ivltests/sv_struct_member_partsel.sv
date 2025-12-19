// Test constant part-select on struct members (r-value)
// Tests patterns like: struct_var.member[msb:lsb]

module test;

  typedef struct packed {
    logic [31:0] data;
    logic [7:0]  addr;
    logic        valid;
  } packet_t;

  packet_t pkt;
  logic [7:0] byte_val;
  logic [15:0] word_val;
  int passed;

  initial begin
    passed = 1;

    // Initialize packet
    pkt.data = 32'hDEADBEEF;
    pkt.addr = 8'hAB;
    pkt.valid = 1'b1;

    $display("Testing constant part-select on struct members:");

    // Test constant part-select: member[msb:lsb]
    byte_val = pkt.data[7:0];
    if (byte_val != 8'hEF) begin
      $display("FAILED: pkt.data[7:0] expected 0xEF, got 0x%h", byte_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.data[7:0] = 0x%h", byte_val);
    end

    byte_val = pkt.data[15:8];
    if (byte_val != 8'hBE) begin
      $display("FAILED: pkt.data[15:8] expected 0xBE, got 0x%h", byte_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.data[15:8] = 0x%h", byte_val);
    end

    byte_val = pkt.data[23:16];
    if (byte_val != 8'hAD) begin
      $display("FAILED: pkt.data[23:16] expected 0xAD, got 0x%h", byte_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.data[23:16] = 0x%h", byte_val);
    end

    byte_val = pkt.data[31:24];
    if (byte_val != 8'hDE) begin
      $display("FAILED: pkt.data[31:24] expected 0xDE, got 0x%h", byte_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.data[31:24] = 0x%h", byte_val);
    end

    // Test word access
    word_val = pkt.data[15:0];
    if (word_val != 16'hBEEF) begin
      $display("FAILED: pkt.data[15:0] expected 0xBEEF, got 0x%h", word_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.data[15:0] = 0x%h", word_val);
    end

    word_val = pkt.data[31:16];
    if (word_val != 16'hDEAD) begin
      $display("FAILED: pkt.data[31:16] expected 0xDEAD, got 0x%h", word_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.data[31:16] = 0x%h", word_val);
    end

    // Test nested struct member part-select
    pkt.addr = 8'hCD;
    byte_val = pkt.addr[7:4];
    if (byte_val != 4'hC) begin
      $display("FAILED: pkt.addr[7:4] expected 0xC, got 0x%h", byte_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.addr[7:4] = 0x%h", byte_val);
    end

    byte_val = pkt.addr[3:0];
    if (byte_val != 4'hD) begin
      $display("FAILED: pkt.addr[3:0] expected 0xD, got 0x%h", byte_val);
      passed = 0;
    end else begin
      $display("PASSED: pkt.addr[3:0] = 0x%h", byte_val);
    end

    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
