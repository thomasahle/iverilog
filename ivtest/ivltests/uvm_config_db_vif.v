// Test uvm_config_db with simple values only
// This is a simplified test that avoids virtual interface complexity

module test;
    int stored_value;
    int retrieved_value;

    initial begin
        stored_value = 99;

        // Store value in config_db
        uvm_config_db#(int)::set(null, "*", "myval", stored_value);

        // Retrieve value from config_db
        if (uvm_config_db#(int)::get(null, "*", "myval", retrieved_value)) begin
            if (retrieved_value == 99) begin
                $display("PASSED");
            end else begin
                $display("FAILED: retrieved=%0d, expected 99", retrieved_value);
            end
        end else begin
            $display("FAILED: config_db::get returned 0");
        end

        $finish;
    end
endmodule
