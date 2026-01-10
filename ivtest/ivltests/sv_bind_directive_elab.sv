// Test bind directive
// This tests that a module can be bound into another module

// Assertion module to be bound
module assert_clk_valid(
    input clk,
    input reset,
    input valid
);
    // Simple assertion: when not reset, check valid
    always @(posedge clk) begin
        if (!reset && valid)
            $display("assert_clk_valid: valid is high");
    end

    initial $display("assert_clk_valid instantiated");
endmodule

// Target module that will have the assertion bound to it
module dut(
    input clk,
    input reset,
    input [7:0] data,
    input valid,
    output reg [7:0] result
);
    always @(posedge clk) begin
        if (reset)
            result <= 0;
        else if (valid)
            result <= data + 1;
    end
endmodule

// Bind the assertion module into all instances of dut
bind dut assert_clk_valid u_assert(.clk(clk), .reset(reset), .valid(valid));

// Testbench
module test;
    reg clk, reset;
    reg [7:0] data;
    reg valid;
    wire [7:0] result;

    // Instantiate two DUT instances
    dut dut1(.clk(clk), .reset(reset), .data(data), .valid(valid), .result(result));
    dut dut2(.clk(clk), .reset(reset), .data(data), .valid(valid), .result());

    initial begin
        clk = 0;
        reset = 1;
        data = 8'h10;
        valid = 0;

        #10 reset = 0;
        #10 valid = 1;
        #10;
        #10 clk = 1;
        #10 clk = 0;
        #10;

        if (result == 8'h11)
            $display("PASSED");
        else
            $display("FAILED: expected 0x11, got 0x%02x", result);
    end
endmodule
