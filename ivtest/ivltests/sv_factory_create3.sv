// Test $ivl_factory_create with unknown type
// Should return null for unregistered type names

class known_class;
  function new();
  endfunction
endclass

module test;
  initial begin
    known_class obj;
    string type_name;

    // Try to create unknown type
    type_name = "unknown_class_xyz";
    obj = $ivl_factory_create(type_name);

    if (obj != null) begin
      $display("FAILED: expected null for unknown type");
      $finish;
    end

    // Now create a known type
    type_name = "known_class";
    obj = $ivl_factory_create(type_name);

    if (obj == null) begin
      $display("FAILED: expected non-null for known type");
      $finish;
    end

    $display("PASSED");
  end
endmodule
