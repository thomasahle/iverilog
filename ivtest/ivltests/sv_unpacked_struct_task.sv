// Test unpacked struct member access in tasks
// This tests if struct members can be read/written in tasks

typedef struct {
  bit [7:0] data;
  bit valid;
  bit [3:0] sel;
} packet_t;

module test;
  packet_t pkt;
  logic [7:0] result_data;
  logic result_valid;
  logic [3:0] result_sel;

  // Task that reads struct members
  task read_packet(input packet_t p, output logic [7:0] d, output logic v, output logic [3:0] s);
    d = p.data;
    v = p.valid;
    s = p.sel;
  endtask

  // Task that writes struct members
  task write_packet(inout packet_t p, input logic [7:0] d, input logic v, input logic [3:0] s);
    p.data = d;
    p.valid = v;
    p.sel = s;
  endtask

  initial begin
    // Initialize struct
    pkt.data = 8'h00;
    pkt.valid = 0;
    pkt.sel = 4'b0000;

    // Write values using task
    write_packet(pkt, 8'hAB, 1'b1, 4'b0101);
    $display("After write_packet: pkt.data=0x%h, pkt.valid=%b, pkt.sel=%b", pkt.data, pkt.valid, pkt.sel);

    // Read values using task
    read_packet(pkt, result_data, result_valid, result_sel);
    $display("After read_packet: result_data=0x%h, result_valid=%b, result_sel=%b",
             result_data, result_valid, result_sel);

    // Verify
    if (pkt.data !== 8'hAB) begin
      $display("FAILED: Expected pkt.data=0xAB, got 0x%h", pkt.data);
      $finish;
    end
    if (pkt.valid !== 1) begin
      $display("FAILED: Expected pkt.valid=1, got %b", pkt.valid);
      $finish;
    end
    if (pkt.sel !== 4'b0101) begin
      $display("FAILED: Expected pkt.sel=0101, got %b", pkt.sel);
      $finish;
    end
    if (result_data !== 8'hAB) begin
      $display("FAILED: Expected result_data=0xAB, got 0x%h", result_data);
      $finish;
    end
    if (result_valid !== 1) begin
      $display("FAILED: Expected result_valid=1, got %b", result_valid);
      $finish;
    end
    if (result_sel !== 4'b0101) begin
      $display("FAILED: Expected result_sel=0101, got %b", result_sel);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
