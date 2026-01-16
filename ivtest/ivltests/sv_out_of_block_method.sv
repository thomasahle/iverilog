// Test out-of-block class method definitions inside modules
// SystemVerilog allows defining class methods outside the class body
// using the ClassName::methodName syntax

module test;
    // Define a class with extern method declarations
    class my_class;
        int value;
        string name;

        extern function void set_value(int v);
        extern function int get_value();
        extern function void set_name(string n);
        extern task display_info();
    endclass

    // Out-of-block function definition with return type
    function void my_class::set_value(int v);
        value = v;
    endfunction

    // Out-of-block function definition with return type
    function int my_class::get_value();
        return value;
    endfunction

    // Out-of-block function with string parameter
    function void my_class::set_name(string n);
        name = n;
    endfunction

    // Out-of-block task definition
    task my_class::display_info();
        $display("name=%s, value=%0d", name, value);
    endtask

    // Test the class with out-of-block methods
    my_class obj;

    initial begin
        obj = new;
        obj.set_name("test_object");
        obj.set_value(42);

        if (obj.get_value() != 42) begin
            $display("FAILED: get_value returned %0d, expected 42", obj.get_value());
            $finish;
        end

        obj.display_info();
        $display("PASSED");
    end
endmodule
