// Test: Interface port member access
// Tests read and write of interface member signals through interface ports

interface simple_if;
    logic [7:0] data;
    logic valid;
endinterface

// Module that reads from interface port members
module consumer(simple_if intf);
    logic [7:0] captured_data;
    logic captured_valid;

    // Read interface port members
    always @* begin
        captured_data = intf.data;
        captured_valid = intf.valid;
    end

    task check_values(input logic [7:0] exp_data, input logic exp_valid);
        if (captured_data !== exp_data || captured_valid !== exp_valid) begin
            $display("FAILED: captured_data=%h (exp %h), captured_valid=%b (exp %b)",
                     captured_data, exp_data, captured_valid, exp_valid);
            $finish;
        end
    endtask
endmodule

// Module that writes to interface port members
module driver(simple_if intf);
    task set_values(input logic [7:0] d, input logic v);
        intf.data = d;
        intf.valid = v;
    endtask
endmodule

module test;
    simple_if sif();

    consumer u_consumer(.intf(sif));
    driver u_driver(.intf(sif));

    initial begin
        // Test 1: Write through driver, read through consumer
        u_driver.set_values(8'hAB, 1'b1);
        #1;
        u_consumer.check_values(8'hAB, 1'b1);

        // Test 2: Different values
        u_driver.set_values(8'hCD, 1'b0);
        #1;
        u_consumer.check_values(8'hCD, 1'b0);

        // Test 3: Zero values
        u_driver.set_values(8'h00, 1'b0);
        #1;
        u_consumer.check_values(8'h00, 1'b0);

        $display("PASSED");
        $finish;
    end
endmodule
