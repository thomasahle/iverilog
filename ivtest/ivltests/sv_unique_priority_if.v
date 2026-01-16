// Test unique if, unique0 if, and priority if statements (SV 12.4.2)
module test;
    reg [3:0] a;
    reg [1:0] b;
    reg [1:0] c;
    reg [1:0] d;

    always @* begin
        // Test unique if - exactly one condition should match
        unique if (a == 0)
            b = 1;
        else if (a == 1)
            b = 2;
        else
            b = 0;

        // Test unique0 if - at most one condition should match (no match ok)
        unique0 if (a == 2)
            c = 1;
        else if (a == 3)
            c = 2;

        // Test priority if - conditions checked in order, first match wins
        priority if (a < 4)
            d = 1;
        else if (a < 8)
            d = 2;
        else
            d = 3;
    end

    initial begin
        // Test case where a==0: unique if takes first branch
        a = 0;
        #1;
        if (b !== 1) begin
            $display("FAILED: unique if a==0, expected b=1, got %d", b);
            $finish;
        end
        if (d !== 1) begin
            $display("FAILED: priority if a==0, expected d=1, got %d", d);
            $finish;
        end

        // Test case where a==5: unique if takes else
        a = 5;
        #1;
        if (b !== 0) begin
            $display("FAILED: unique if a==5, expected b=0, got %d", b);
            $finish;
        end
        if (d !== 2) begin
            $display("FAILED: priority if a==5, expected d=2, got %d", d);
            $finish;
        end

        // Test case where a==10: priority if takes last else
        a = 10;
        #1;
        if (d !== 3) begin
            $display("FAILED: priority if a==10, expected d=3, got %d", d);
            $finish;
        end

        $display("PASSED");
    end
endmodule
