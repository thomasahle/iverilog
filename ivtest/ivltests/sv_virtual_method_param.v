// Test virtual method dispatch with object parameters
// Tests passing derived class objects through function parameters
// and ensuring virtual dispatch works correctly

class item_base;
    int id;

    function new(int _id);
        id = _id;
    endfunction

    virtual function string get_type_name();
        return "item_base";
    endfunction

    virtual function int get_value();
        return id;
    endfunction
endclass

class item_derived extends item_base;
    int extra_value;

    function new(int _id, int _extra);
        super.new(_id);
        extra_value = _extra;
    endfunction

    virtual function string get_type_name();
        return "item_derived";
    endfunction

    virtual function int get_value();
        return id + extra_value;
    endfunction
endclass

// Static function that takes base class parameter but receives derived
function automatic string process_item(item_base item);
    return item.get_type_name();
endfunction

// Task that takes base class parameter but receives derived
task automatic process_item_task(item_base item, output int result);
    result = item.get_value();
endtask

module test;
    item_base base_item;
    item_derived derived_item;
    int errors;
    string type_name;
    int value;

    initial begin
        errors = 0;

        // Test 1: Direct call on derived object
        derived_item = new(10, 5);
        type_name = derived_item.get_type_name();
        if (type_name != "item_derived") begin
            $display("FAILED Test 1: Expected 'item_derived', got '%s'", type_name);
            errors++;
        end

        // Test 2: Call through base reference
        base_item = derived_item;
        type_name = base_item.get_type_name();
        if (type_name != "item_derived") begin
            $display("FAILED Test 2: Expected 'item_derived', got '%s'", type_name);
            errors++;
        end

        // Test 3: Pass derived object to function taking base
        derived_item = new(20, 10);
        type_name = process_item(derived_item);
        if (type_name != "item_derived") begin
            $display("FAILED Test 3: Expected 'item_derived', got '%s'", type_name);
            errors++;
        end

        // Test 4: Pass through task with output
        derived_item = new(100, 50);
        process_item_task(derived_item, value);
        if (value != 150) begin
            $display("FAILED Test 4: Expected 150, got %0d", value);
            errors++;
        end

        // Test 5: Multiple levels of function calls
        base_item = new(5);
        type_name = process_item(base_item);
        if (type_name != "item_base") begin
            $display("FAILED Test 5: Expected 'item_base', got '%s'", type_name);
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
