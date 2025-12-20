// Test: $cast with method call returning class object as argument
// This tests using $cast as a task with a clone() or similar method as the source

class Base;
    int value;
    
    function new(int v = 0);
        value = v;
    endfunction
    
    // Clone method that returns a new object
    virtual function Base clone();
        Base ret = new();
        ret.value = this.value;
        return ret;
    endfunction
    
    virtual function string get_type();
        return "Base";
    endfunction
endclass

class Derived extends Base;
    int extra;
    
    function new(int v = 0, int e = 0);
        super.new(v);
        extra = e;
    endfunction
    
    // Override clone to return correct type
    virtual function Base clone();
        Derived ret = new();
        ret.value = this.value;
        ret.extra = this.extra;
        return ret;
    endfunction
    
    virtual function string get_type();
        return "Derived";
    endfunction
endclass

module test;
    Base b, b_clone;
    Derived d, d_clone;
    int result;
    
    initial begin
        // Test 1: $cast as task with clone() - Base to Base
        b = new(42);
        $cast(b_clone, b.clone());
        
        if (b_clone == null) begin
            $display("Test 1 FAILED: b_clone is null");
            $finish;
        end
        if (b_clone.value != 42) begin
            $display("Test 1 FAILED: Expected value=42, got %0d", b_clone.value);
            $finish;
        end
        $display("Test 1 PASSED: $cast(base, base.clone()) works");
        
        // Test 2: $cast as task with clone() - Derived to Base
        d = new(100, 200);
        $cast(b_clone, d.clone());
        
        if (b_clone == null) begin
            $display("Test 2 FAILED: b_clone is null");
            $finish;
        end
        if (b_clone.value != 100) begin
            $display("Test 2 FAILED: Expected value=100, got %0d", b_clone.value);
            $finish;
        end
        $display("Test 2 PASSED: $cast(base, derived.clone()) works");
        
        // Test 3: $cast as task with clone() - Derived clone to Derived
        $cast(d_clone, d.clone());
        
        if (d_clone == null) begin
            $display("Test 3 FAILED: d_clone is null");
            $finish;
        end
        if (d_clone.value != 100 || d_clone.extra != 200) begin
            $display("Test 3 FAILED: Expected value=100,extra=200, got %0d,%0d", 
                     d_clone.value, d_clone.extra);
            $finish;
        end
        $display("Test 3 PASSED: $cast(derived, derived.clone()) works");
        
        // Test 4: $cast as function (should still work)
        b = new(77);
        result = $cast(b_clone, b.clone());
        
        if (result != 1) begin
            $display("Test 4 FAILED: $cast function returned %0d, expected 1", result);
            $finish;
        end
        if (b_clone.value != 77) begin
            $display("Test 4 FAILED: Expected value=77, got %0d", b_clone.value);
            $finish;
        end
        $display("Test 4 PASSED: $cast as function with clone() works");
        
        $display("PASSED");
        $finish;
    end
endmodule
