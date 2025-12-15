// Test virtual method dispatch through wrapper methods
// Tests the fix for virtual methods not dispatching correctly
// when called through a non-virtual wrapper method

class base;
    int called_base;
    int called_derived;

    function new();
        called_base = 0;
        called_derived = 0;
    endfunction

    // Virtual method that derived class overrides
    virtual function void do_something();
        called_base = 1;
    endfunction

    // Non-virtual wrapper that calls virtual method
    function void wrapper();
        do_something();  // Should dispatch to derived if obj is derived
    endfunction
endclass

class derived extends base;
    virtual function void do_something();
        called_derived = 1;
    endfunction
endclass

module test;
    base b;
    derived d;
    int errors;

    initial begin
        errors = 0;

        // Test direct call on base object
        b = new();
        b.wrapper();
        if (b.called_base != 1) begin
            $display("FAILED: base.wrapper() didn't call base.do_something()");
            errors++;
        end

        // Test direct call on derived object
        d = new();
        d.wrapper();
        if (d.called_derived != 1) begin
            $display("FAILED: derived.wrapper() didn't call derived.do_something()");
            errors++;
        end

        // Test polymorphic call: base reference to derived object
        b = new();  // Reset
        d = new();
        b = d;  // Base reference to derived object
        b.wrapper();  // Should dispatch to derived.do_something()
        if (d.called_derived != 1) begin
            $display("FAILED: base_ref.wrapper() didn't dispatch to derived.do_something()");
            errors++;
        end

        if (errors == 0) begin
            $display("PASSED");
        end else begin
            $display("FAILED: %0d errors", errors);
        end

        $finish;
    end
endmodule
