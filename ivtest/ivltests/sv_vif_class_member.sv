// Test: Virtual interface with class-typed member
// Tests assigning a class object to a VIF member (uses %vif/store/obj opcode)

interface driver_bfm;
    logic [7:0] data;
    
    // Class-typed member in the interface
    class proxy_base;
        int id;
        function new(int i);
            id = i;
        endfunction
    endclass
    
    proxy_base proxy_h;
    
    task set_proxy(proxy_base p);
        proxy_h = p;
    endtask
    
    function int get_proxy_id();
        if (proxy_h != null)
            return proxy_h.id;
        else
            return -1;
    endfunction
endinterface

// Proxy class that will be stored in the VIF
class driver_proxy;
    int value;
    virtual driver_bfm vif;
    
    function new(int v);
        value = v;
    endfunction
    
    // This is the key pattern: assigning 'this' to a VIF class member
    task connect(virtual driver_bfm v);
        vif = v;
        // Store this object in the VIF's proxy_h member
        // This requires the %vif/store/obj opcode
        vif.proxy_h = new driver_bfm::proxy_base(value);
    endtask
    
    function int get_id();
        return vif.get_proxy_id();
    endfunction
endclass

module test;
    driver_bfm bfm();
    driver_proxy proxy;
    
    initial begin
        // Create proxy with value 42
        proxy = new(42);
        
        // Connect proxy to BFM - this stores a class object to VIF member
        proxy.connect(bfm);
        
        // Verify the proxy was stored correctly
        if (proxy.get_id() == 42) begin
            $display("PASSED: VIF class member assignment works");
        end else begin
            $display("FAILED: Expected id=42, got %0d", proxy.get_id());
        end
        
        $finish;
    end
endmodule
