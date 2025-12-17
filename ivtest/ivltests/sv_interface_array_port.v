// Test interface array port binding in generate block
interface simple_if(input logic clk);
  logic data;
  logic valid;

  task set_data(input logic d);
    data = d;
  endtask
endinterface

module sub_mod #(parameter INST_ID = 0) (simple_if intf);
  initial begin
    #10 $display("sub_mod[%0d]: intf.data=%b, intf.valid=%b", INST_ID, intf.data, intf.valid);
  end
endmodule

module top;
  logic clk;

  // Interface array declaration
  simple_if intf_arr[2](clk);

  // Generate block with genvar indexing interface array
  genvar i;
  generate
    for (i = 0; i < 2; i++) begin : gen_sub
      sub_mod #(.INST_ID(i)) sub_inst(intf_arr[i]);
    end
  endgenerate

  initial begin
    clk = 0;
    intf_arr[0].data = 1;
    intf_arr[0].valid = 1;
    intf_arr[1].data = 0;
    intf_arr[1].valid = 1;
    #20 $display("PASSED");
    $finish;
  end
endmodule
