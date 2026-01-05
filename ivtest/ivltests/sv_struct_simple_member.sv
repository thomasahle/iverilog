// Test simple packed struct member access
module test;
  typedef struct packed {
    logic [7:0] header;
    logic [31:0] data;
    logic [7:0] footer;
  } packet_t;

  packet_t pkt;
  logic [31:0] read_val;

  initial begin
    pkt.header = 8'hAA;
    pkt.data = 32'h12345678;
    pkt.footer = 8'h55;

    read_val = pkt.data;
    if (read_val !== 32'h12345678) begin
      $display("FAILED: pkt.data = %h, expected 12345678", read_val);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
