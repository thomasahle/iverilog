// Test: Direct interface task and function calls
// Tests calling tasks/functions defined in an interface from a direct interface instance

interface simple_if;
    logic [7:0] data;
    logic valid;

    // Task defined in the interface
    task set_data(input logic [7:0] value);
        data = value;
        valid = 1'b1;
    endtask

    // Function defined in the interface
    function logic [7:0] get_data();
        return data;
    endfunction
endinterface

module test;
    simple_if sif();
    logic [7:0] read_val;

    initial begin
        // Test 1: Direct call to interface task
        sif.set_data(8'hAB);
        #1;
        if (sif.data !== 8'hAB || sif.valid !== 1'b1) begin
            $display("FAILED: After set_data(0xAB): data=%h (exp AB), valid=%b (exp 1)",
                     sif.data, sif.valid);
            $finish;
        end

        // Test 2: Direct call to interface function
        read_val = sif.get_data();
        if (read_val !== 8'hAB) begin
            $display("FAILED: get_data() returned %h, expected AB", read_val);
            $finish;
        end

        // Test 3: Call task again with different value
        sif.set_data(8'hCD);
        #1;
        if (sif.data !== 8'hCD) begin
            $display("FAILED: After set_data(0xCD): data=%h, expected CD", sif.data);
            $finish;
        end

        $display("PASSED");
        $finish;
    end
endmodule
