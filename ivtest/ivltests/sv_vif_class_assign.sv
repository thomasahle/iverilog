// Test: Assigning class object to virtual interface member
// This tests the %vif/store/obj opcode

class MyClass;
    int value;
    function new(int v);
        value = v;
    endfunction
endclass

interface simple_if;
    MyClass obj_handle;
    
    function int get_value();
        if (obj_handle != null)
            return obj_handle.value;
        else
            return -1;
    endfunction
endinterface

class Driver;
    virtual simple_if vif;
    
    function new(virtual simple_if v);
        vif = v;
    endfunction
    
    // Store a class object in the VIF member
    task store_object(MyClass obj);
        vif.obj_handle = obj;
    endtask
    
    // Store 'this' pattern - common in UVM
    task store_self();
        MyClass self_obj = new(999);
        vif.obj_handle = self_obj;
    endtask
endclass

module test;
    simple_if sif();
    Driver drv;
    MyClass my_obj;
    
    initial begin
        drv = new(sif);
        
        // Test 1: Store an external class object
        my_obj = new(42);
        drv.store_object(my_obj);
        
        if (sif.get_value() == 42) begin
            $display("Test 1 PASSED: External object stored correctly");
        end else begin
            $display("Test 1 FAILED: Expected 42, got %0d", sif.get_value());
            $finish;
        end
        
        // Test 2: Store a different object
        my_obj = new(100);
        drv.store_object(my_obj);
        
        if (sif.get_value() == 100) begin
            $display("Test 2 PASSED: Object replaced correctly");
        end else begin
            $display("Test 2 FAILED: Expected 100, got %0d", sif.get_value());
            $finish;
        end
        
        // Test 3: Store from within the class
        drv.store_self();
        
        if (sif.get_value() == 999) begin
            $display("Test 3 PASSED: Self-created object stored correctly");
        end else begin
            $display("Test 3 FAILED: Expected 999, got %0d", sif.get_value());
            $finish;
        end
        
        $display("PASSED");
        $finish;
    end
endmodule
