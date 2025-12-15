// Test UVM factory pattern - create class by name
// Tests $ivl_factory_create system function

class simple_class;
    int value;

    function new();
        value = 42;
    endfunction
endclass

module test;
    simple_class obj;
    string type_name;

    initial begin
        // Create object using factory by class name
        type_name = "simple_class";
        obj = $ivl_factory_create(type_name);

        if (obj != null) begin
            if (obj.value == 42) begin
                $display("PASSED");
            end else begin
                $display("FAILED: obj.value=%0d, expected 42", obj.value);
            end
        end else begin
            $display("FAILED: factory_create returned null");
        end

        $finish;
    end
endmodule
