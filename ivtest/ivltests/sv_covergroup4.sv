// Test covergroup with event trigger syntax
// This test verifies covergroups with @(event) trigger syntax.

class state_monitor;
  logic [3:0] state;
  logic [7:0] count;

  // Covergroup with event trigger syntax
  covergroup state_cg @(state);
    option.per_instance = 1;

    STATE_CP : coverpoint state {
      bins IDLE = {4'b0000};
      bins INIT = {4'b0001};
      bins RUN = {4'b0010};
      bins DONE = {4'b0100};
      bins ERROR = {4'b1000};
      illegal_bins INVALID = default;
    }

    COUNT_CP : coverpoint count {
      bins SMALL = {[0:15]};
      bins MEDIUM = {[16:127]};
      bins LARGE = {[128:255]};
    }
  endgroup
endclass

module test;
  initial begin
    $display("PASSED");
  end
endmodule
