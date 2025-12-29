// Test pattern similar to UVM's converter/from_class pattern
// This tests passing objects through automatic scopes and
// ensuring virtual method dispatch works correctly

class seq_item_base;
    int id;
    int data;

    function new();
        id = 0;
        data = 0;
    endfunction

    virtual function void do_copy(seq_item_base rhs);
        id = rhs.id;
        data = rhs.data;
    endfunction

    virtual function int get_data_size();
        return 32;  // base size
    endfunction
endclass

class seq_item_derived extends seq_item_base;
    int extra_field;

    function new();
        super.new();
        extra_field = 0;
    endfunction

    virtual function void do_copy(seq_item_base rhs);
        seq_item_derived rhs_d;
        super.do_copy(rhs);
        if ($cast(rhs_d, rhs)) begin
            extra_field = rhs_d.extra_field;
        end
    endfunction

    virtual function int get_data_size();
        return 64;  // derived has more data
    endfunction
endclass

// Converter class (like UVM's uvm_packer/converter)
class converter #(type T = seq_item_base);
    static function void from_class(T item);
        int size;
        size = item.get_data_size();
        $display("Converter: item type has data_size=%0d", size);
    endfunction
endclass

// Derived converter
class derived_converter extends converter #(seq_item_derived);
    static function void from_class(seq_item_derived item);
        $display("Derived converter: id=%0d data=%0d extra=%0d size=%0d",
                 item.id, item.data, item.extra_field, item.get_data_size());
    endfunction
endclass

// Driver proxy that holds a request and calls converter
class driver_proxy;
    seq_item_base req;

    function void set_req(seq_item_base item);
        req = item;
    endfunction

    // This pattern is like UVM's driver getting an item and converting
    task get_and_convert();
        seq_item_derived derived_item;
        if (req != null) begin
            $display("get_and_convert: req.get_data_size()=%0d", req.get_data_size());
            // Try to convert through derived
            if ($cast(derived_item, req)) begin
                derived_converter::from_class(derived_item);
            end else begin
                converter#(seq_item_base)::from_class(req);
            end
        end
    endtask
endclass

module test;
    driver_proxy driver;
    seq_item_derived item;
    int errors;

    initial begin
        errors = 0;

        // Create driver and item
        driver = new();
        item = new();
        item.id = 42;
        item.data = 100;
        item.extra_field = 500;

        // Set request (derived stored as base)
        driver.set_req(item);

        // Verify req can dispatch virtually
        if (driver.req.get_data_size() != 64) begin
            $display("FAILED: Expected data_size=64, got %0d", driver.req.get_data_size());
            errors++;
        end

        // Call converter pattern
        driver.get_and_convert();

        if (errors == 0) begin
            $display("PASSED");
        end else begin
            $display("FAILED: %0d errors", errors);
        end

        $finish;
    end
endmodule
