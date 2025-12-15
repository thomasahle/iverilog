// Check virtual interface read access (r-value)
// Test that a class can read from virtual interface members

interface simple_if;
    logic [7:0] data;
    logic valid;
endinterface

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
    vif_monitor mon;

    initial begin
        mon = new();
        mon.vif = u_if;

        // Set values directly on interface
        u_if.data = 8'h55;
        u_if.valid = 1'b1;
        #1;

        // Read through VIF
        if (mon.read_data() == 8'h55 && mon.read_valid() == 1'b1) begin
            $display("PASSED");
        end else begin
            $display("FAILED: data=%h valid=%b", mon.read_data(), mon.read_valid());
        end
    end
endmodule
