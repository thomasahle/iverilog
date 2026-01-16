// Test SystemVerilog statement labels (SV 9.3.5)
// Prefix statement labels: label: begin/fork ... end/join: label
module test;
    reg a, b, c, d;
    reg [7:0] result;

    initial begin
        result = 0;

        // Test prefix label on begin block
        seq_block: begin
            a = 1;
            b = 1;
            result = result + 1;
        end: seq_block

        // Test prefix label on fork block
        par_block: fork
            #1 c = 1;
            #1 d = 1;
        join: par_block
        result = result + 1;

        // Nested labeled blocks
        outer: begin
            inner: begin
                result = result + 1;
            end: inner
        end: outer

        #2;
        if (a !== 1 || b !== 1 || c !== 1 || d !== 1) begin
            $display("FAILED: values not set correctly");
            $finish;
        end
        if (result !== 3) begin
            $display("FAILED: result = %d, expected 3", result);
            $finish;
        end
        $display("PASSED");
    end
endmodule
