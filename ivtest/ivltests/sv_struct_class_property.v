// Test struct-typed class properties
// Tests: obj.struct_prop.member access (both l-value and r-value)

typedef struct {
  int a;
  int b;
  logic [7:0] c;
} my_struct_t;

class my_class;
  my_struct_t data;
  int id;

  function new(int i);
    id = i;
    data.a = 0;
    data.b = 0;
    data.c = 0;
  endfunction

  function void set_struct(int va, int vb, logic [7:0] vc);
    data.a = va;
    data.b = vb;
    data.c = vc;
  endfunction

  function int get_sum();
    return data.a + data.b;
  endfunction
endclass

module test;
  my_class obj;
  int val;
  int errors = 0;

  initial begin
    obj = new(42);

    // Test l-value: write to struct members through class property
    obj.data.a = 100;
    obj.data.b = 200;
    obj.data.c = 8'hAB;

    // Test r-value: read struct members through class property
    val = obj.data.a;
    if (val != 100) begin
      $display("FAILED: obj.data.a = %0d, expected 100", val);
      errors++;
    end

    val = obj.data.b;
    if (val != 200) begin
      $display("FAILED: obj.data.b = %0d, expected 200", val);
      errors++;
    end

    if (obj.data.c != 8'hAB) begin
      $display("FAILED: obj.data.c = %h, expected AB", obj.data.c);
      errors++;
    end

    // Test method that uses struct internally
    val = obj.get_sum();
    if (val != 300) begin
      $display("FAILED: get_sum() = %0d, expected 300", val);
      errors++;
    end

    // Test using method to set struct values
    obj.set_struct(50, 60, 8'hCD);

    val = obj.data.a;
    if (val != 50) begin
      $display("FAILED: After set_struct, obj.data.a = %0d, expected 50", val);
      errors++;
    end

    val = obj.data.b;
    if (val != 60) begin
      $display("FAILED: After set_struct, obj.data.b = %0d, expected 60", val);
      errors++;
    end

    // Test struct member in conditional
    if (obj.data.a == 50 && obj.data.b == 60) begin
      // OK
    end else begin
      $display("FAILED: Conditional check on struct members");
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
    $finish;
  end
endmodule
