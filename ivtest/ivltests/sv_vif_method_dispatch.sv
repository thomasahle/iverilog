// Test: Virtual interface method dispatch
// Tests calling tasks/functions through virtual interface in a class

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

// Driver class using virtual interface
class driver;
    virtual simple_if vif;

    function new(virtual simple_if v);
        vif = v;
    endfunction

    task drive_data(logic [7:0] value);
        // Call task through virtual interface
        vif.set_data(value);
    endtask

    function logic [7:0] read_data();
        // Call function through virtual interface
        return vif.get_data();
    endfunction
endclass

module test;
    simple_if sif();
    driver drv;
    logic [7:0] read_val;

    initial begin
        drv = new(sif);

        // Test 1: Task call through VIF
        drv.drive_data(8'hAB);
        #1;
        if (sif.data !== 8'hAB || sif.valid !== 1'b1) begin
            $display("FAILED: After drive_data(0xAB): data=%h (exp AB), valid=%b (exp 1)",
                     sif.data, sif.valid);
            $finish;
        end

        // Test 2: Function call through VIF
        read_val = drv.read_data();
        if (read_val !== 8'hAB) begin
            $display("FAILED: read_data() returned %h, expected AB", read_val);
            $finish;
        end

        // Test 3: Another task call
        drv.drive_data(8'hCD);
        #1;
        if (sif.data !== 8'hCD) begin
            $display("FAILED: After drive_data(0xCD): data=%h, expected CD", sif.data);
            $finish;
        end

        $display("PASSED");
        $finish;
    end
endmodule
