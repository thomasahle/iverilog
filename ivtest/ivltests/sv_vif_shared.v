// Check that multiple virtual interfaces can share the same interface instance
// Test driver/monitor pattern with shared interface

interface simple_if;
    logic [7:0] data;
    logic valid;
endinterface

class vif_driver;
    virtual simple_if vif;

    function new();
    endfunction

    function void drive(logic [7:0] d, logic v);
        vif.data = d;
        vif.valid = v;
    endfunction
endclass

class vif_monitor;
    virtual simple_if vif;

    function new();
    endfunction

    function logic [7:0] read_data();
        return vif.data;
    endfunction

    function logic read_valid();
        return vif.valid;
    endfunction
endclass

module test;
    simple_if u_if();

    vif_driver drv;
    vif_monitor mon;

    initial begin
        // Initialize interface directly (ensures signals are elaborated)
        u_if.data = 8'h00;
        u_if.valid = 1'b0;

        drv = new();
        mon = new();

        // Both point to same interface
        drv.vif = u_if;
        mon.vif = u_if;

        // Write through driver
        drv.drive(8'hCD, 1'b1);
        #1;

        // Read through monitor - should see driver's writes
        if (mon.read_data() == 8'hCD && mon.read_valid() == 1'b1) begin
            $display("PASSED");
        end else begin
            $display("FAILED: data=%h valid=%b", mon.read_data(), mon.read_valid());
        end
    end
endmodule
