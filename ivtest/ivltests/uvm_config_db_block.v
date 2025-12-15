// Test uvm_config_db at start of block (block_item_decl context)
// This tests the parser fix where config_db::set() at the start of
// an initial block was being consumed by block_item_decl instead of
// being treated as a statement.

module test;
    int value1;
    int value2;

    // This is the key test: config_db::set as first statement in initial block
    // The parser must correctly route this to statement handling, not declaration handling
    initial begin
        uvm_config_db#(int)::set(null, "*", "test_val", 123);

        // Now try to retrieve it
        if (uvm_config_db#(int)::get(null, "*", "test_val", value1)) begin
            if (value1 == 123) begin
                $display("PASSED");
            end else begin
                $display("FAILED: value1=%0d, expected 123", value1);
            end
        end else begin
            $display("FAILED: config_db::get returned 0");
        end

        $finish;
    end
endmodule
