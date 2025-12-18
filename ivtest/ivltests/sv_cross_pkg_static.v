// Test cross-package static method calls
// When a static method is called via ClassName::method() and the
// class is accessed through a wildcard import (import pkg::*),
// the method should be found properly.

package global_pkg;
  parameter int WIDTH = 32;

  typedef struct {
    bit [WIDTH-1:0] data;
    bit [3:0] addr;
  } transfer_t;
endpackage

package converter_pkg;
  import global_pkg::*;

  class tx_item;
    bit [WIDTH-1:0] data;
    bit [3:0] addr;
  endclass

  class seq_item_converter;
    extern static function void from_class(input tx_item in_item, output transfer_t out);
    extern static function void to_class(input transfer_t in_pkt, ref tx_item out_item);
  endclass

  function void seq_item_converter::from_class(input tx_item in_item, output transfer_t out);
    out.data = in_item.data;
    out.addr = in_item.addr;
  endfunction

  function void seq_item_converter::to_class(input transfer_t in_pkt, ref tx_item out_item);
    out_item.data = in_pkt.data;
    out_item.addr = in_pkt.addr;
  endfunction
endpackage

package driver_pkg;
  import global_pkg::*;
  import converter_pkg::*;

  class driver;
    tx_item req;

    task run();
      transfer_t struct_packet;
      req = new();
      req.data = 32'hDEADBEEF;
      req.addr = 4'hA;

      // Cross-package static method call
      seq_item_converter::from_class(req, struct_packet);
      if (struct_packet.data !== 32'hDEADBEEF) begin
        $display("FAILED: from_class data mismatch");
        $finish;
      end
      if (struct_packet.addr !== 4'hA) begin
        $display("FAILED: from_class addr mismatch");
        $finish;
      end

      struct_packet.data = 32'hCAFEBABE;
      struct_packet.addr = 4'hB;
      seq_item_converter::to_class(struct_packet, req);
      if (req.data !== 32'hCAFEBABE) begin
        $display("FAILED: to_class data mismatch");
        $finish;
      end
      if (req.addr !== 4'hB) begin
        $display("FAILED: to_class addr mismatch");
        $finish;
      end
    endtask
  endclass
endpackage

module test;
  import driver_pkg::*;

  initial begin
    driver d = new();
    d.run();
    $display("PASSED");
    $finish;
  end
endmodule
