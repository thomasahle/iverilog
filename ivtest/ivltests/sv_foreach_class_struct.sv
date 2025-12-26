// Test foreach with struct member arrays inside class methods
// This verifies that foreach correctly identifies array dimensions
// from struct-type class properties.

typedef struct {
  int data[4];
  int values[8];
} my_struct_t;

class my_class;
  my_struct_t s;
  int count;

  function void count_data();
    count = 0;
    foreach(s.data[i]) begin
      count = count + 1;
    end
  endfunction

  function void count_values();
    count = 0;
    foreach(s.values[j]) begin
      count = count + 1;
    end
  endfunction
endclass

module test;
  initial begin
    my_class obj;
    obj = new();

    // Test foreach on s.data (4 elements)
    obj.count_data();
    if (obj.count != 4) begin
      $display("FAILED: data count=%0d, expected 4", obj.count);
      $finish;
    end

    // Test foreach on s.values (8 elements)
    obj.count_values();
    if (obj.count != 8) begin
      $display("FAILED: values count=%0d, expected 8", obj.count);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
