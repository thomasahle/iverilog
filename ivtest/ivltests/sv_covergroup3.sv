// Test covergroup with cross coverage and various bin types
// This test verifies cross coverage and ignore_bins parsing.

class packet;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  rand bit       valid;
endclass

class coverage;
  covergroup cg with function sample(packet p);
    option.per_instance = 1;

    ADDR_CP : coverpoint p.addr {
      bins LOW = {[0:63]};
      bins MID = {[64:191]};
      bins HIGH = {[192:255]};
      ignore_bins RESERVED = {[240:255]};  // Ignored bins
    }

    DATA_CP : coverpoint p.data {
      bins ZERO = {0};
      bins ONES = {8'hFF};
      bins OTHER = default;
    }

    VALID_CP : coverpoint p.valid {
      bins ACTIVE = {1};
      bins INACTIVE = {0};
    }

    // Cross coverage between address and data
    ADDR_X_DATA : cross ADDR_CP, DATA_CP;

    // Cross coverage between address and valid
    ADDR_X_VALID : cross ADDR_CP, VALID_CP;
  endgroup
endclass

module test;
  initial begin
    $display("PASSED");
  end
endmodule
