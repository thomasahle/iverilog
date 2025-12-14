// Test SystemVerilog inside operator
// Tests value inside set and range matching

module test;
    int x;
    int errors;

    initial begin
        errors = 0;

        // Test single values
        x = 5;
        if (!(x inside {1, 2, 3, 4, 5})) begin
            $display("FAILED: 5 should be inside {1,2,3,4,5}");
            errors++;
        end

        x = 6;
        if (x inside {1, 2, 3, 4, 5}) begin
            $display("FAILED: 6 should NOT be inside {1,2,3,4,5}");
            errors++;
        end

        // Test ranges
        x = 10;
        if (!(x inside {[1:5], [10:20]})) begin
            $display("FAILED: 10 should be inside {[1:5], [10:20]}");
            errors++;
        end

        x = 25;
        if (x inside {[1:5], [10:20]}) begin
            $display("FAILED: 25 should NOT be inside {[1:5], [10:20]}");
            errors++;
        end

        // Test mixed values and ranges
        x = 100;
        if (!(x inside {1, 2, [50:60], 100, [200:300]})) begin
            $display("FAILED: 100 should be inside {1,2,[50:60],100,[200:300]}");
            errors++;
        end

        x = 55;
        if (!(x inside {1, 2, [50:60], 100, [200:300]})) begin
            $display("FAILED: 55 should be inside {1,2,[50:60],100,[200:300]}");
            errors++;
        end

        x = 75;
        if (x inside {1, 2, [50:60], 100, [200:300]}) begin
            $display("FAILED: 75 should NOT be inside {1,2,[50:60],100,[200:300]}");
            errors++;
        end

        if (errors == 0) begin
            $display("PASSED");
        end else begin
            $display("FAILED: %0d errors", errors);
        end

        $finish;
    end
endmodule
