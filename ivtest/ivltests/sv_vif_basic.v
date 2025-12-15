// Check basic virtual interface assignment and member access
// Test that a class can store a virtual interface and access its members

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

module test;
    simple_if u_if();
    vif_driver drv;

    initial begin
        drv = new();
        drv.vif = u_if;

        // Write through VIF
        drv.drive(8'hAB, 1'b1);
        #1;

        // Check values
        if (u_if.data == 8'hAB && u_if.valid == 1'b1) begin
            $display("PASSED");
        end else begin
            $display("FAILED: data=%h valid=%b", u_if.data, u_if.valid);
        end
    end
endmodule
