// Test fork/join_none in class task
// Tests the fix for fork/join_none assertion failure in automatic scopes

class runner;
    int count;

    function new();
        count = 0;
    endfunction

    task automatic run();
        fork
            begin
                #10;
                count = count + 1;
            end
        join_none
    endtask

    task automatic run_multiple();
        fork
            begin
                #5;
                count = count + 10;
            end
            begin
                #5;
                count = count + 20;
            end
        join_none
    endtask
endclass

module test;
    runner r;

    initial begin
        r = new();

        // Test single fork/join_none
        r.run();
        #20;
        if (r.count != 1) begin
            $display("FAILED: count=%0d after run(), expected 1", r.count);
            $finish;
        end

        // Reset and test multiple forks
        r.count = 0;
        r.run_multiple();
        #20;
        if (r.count != 30) begin
            $display("FAILED: count=%0d after run_multiple(), expected 30", r.count);
            $finish;
        end

        $display("PASSED");
        $finish;
    end
endmodule
