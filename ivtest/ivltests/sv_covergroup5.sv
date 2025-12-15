// Test covergroup with iff conditions
// This test verifies conditional coverpoints and bins parsing.

class transaction;
  rand bit [7:0] data;
  rand bit       enable;
  rand bit [1:0] mode;
endclass

class coverage;
  covergroup cg with function sample(transaction t);
    option.per_instance = 1;

    // Coverpoint with iff condition
    DATA_CP : coverpoint t.data iff (t.enable) {
      bins LOW = {[0:127]};
      bins HIGH = {[128:255]};
    }

    MODE_CP : coverpoint t.mode {
      bins MODE0 = {0};
      bins MODE1 = {1};
      bins MODE2 = {2};
      bins MODE3 = {3};
    }

    // Cross with iff condition
    DATA_X_MODE : cross DATA_CP, MODE_CP iff (t.enable);
  endgroup
endclass

module test;
  initial begin
    $display("PASSED");
  end
endmodule
