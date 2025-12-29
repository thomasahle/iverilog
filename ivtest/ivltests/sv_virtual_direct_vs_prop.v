// Test to compare direct virtual calls vs property-based calls

class base;
    virtual function string speak();
        return "base";
    endfunction
endclass

class derived extends base;
    virtual function string speak();
        return "derived";
    endfunction
endclass

module test;
    derived d;
    base b;
    string result;
    int errors;

    initial begin
        errors = 0;
        d = new();

        // Test 1: Direct call on derived object
        result = d.speak();
        if (result != "derived") begin
            $display("FAILED Test 1: Direct call returned '%s' instead of 'derived'", result);
            errors++;
        end

        // Test 2: Call through base reference
        b = d;
        result = b.speak();
        if (result != "derived") begin
            $display("FAILED Test 2: Base reference call returned '%s' instead of 'derived'", result);
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
