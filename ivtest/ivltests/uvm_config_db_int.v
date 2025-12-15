// Test uvm_config_db with integer values
// Tests set() and get() for basic data types

module test;
    int stored_value;
    int retrieved_value;

    initial begin
        stored_value = 42;

        // Store value in config_db
        uvm_config_db#(int)::set(null, "*", "myval", stored_value);

        // Retrieve value from config_db
        if (uvm_config_db#(int)::get(null, "*", "myval", retrieved_value)) begin
            if (retrieved_value == 42) begin
                $display("PASSED");
            end else begin
                $display("FAILED: retrieved_value=%0d, expected 42", retrieved_value);
            end
        end else begin
            $display("FAILED: config_db::get returned 0");
        end

        $finish;
    end
endmodule
