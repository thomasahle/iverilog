// Test basic covergroup parsing
// This test verifies that covergroup declarations are parsed correctly.
// Note: Covergroups are parsed but not yet functionally implemented.

class transaction;
  rand bit [7:0] data;
  rand bit [3:0] addr;
  rand int count;
endclass

class coverage;
  // Basic covergroup inside class with sample parameters
  covergroup cg with function sample(transaction t);
    option.per_instance = 1;

    DATA_CP : coverpoint t.data {
      option.comment = "Data value coverage";
      bins LOW = {[0:50]};
      bins MID = {[51:200]};
      bins HIGH = {[201:255]};
    }

    ADDR_CP : coverpoint t.addr {
      bins VALID = {[0:10]};
      bins RESERVED = {[11:15]};
    }

    COUNT_CP : coverpoint t.count {
      bins SMALL = {[0:99]};
      bins LARGE = {[100:999]};
      illegal_bins TOO_LARGE = {[1000:$]};  // Unbounded upper limit
    }

    // Cross coverage
    ADDR_X_DATA : cross ADDR_CP, DATA_CP;
  endgroup

  bit [7:0] data;
  bit [3:0] addr;
endclass

module test;
  coverage cov;
  initial begin
    cov = new();
    cov.data = 100;
    cov.addr = 5;
    $display("PASSED");
  end
endmodule
