// Test foreach with this.array in nested class scenarios
// Tests inheritance and property access patterns

class BaseContainer;
  int base_data[3];

  function new();
    int i;
    for (i = 0; i < 3; i++) base_data[i] = i + 100;
  endfunction

  function int base_sum();
    int total = 0;
    foreach (this.base_data[i]) begin
      total = total + this.base_data[i];
    end
    return total;
  endfunction
endclass

class DerivedContainer extends BaseContainer;
  int derived_data[4];

  function new();
    int i;
    super.new();
    for (i = 0; i < 4; i++) derived_data[i] = i * 10;
  endfunction

  // Test foreach on derived class array
  function int derived_sum();
    int total = 0;
    foreach (this.derived_data[i]) begin
      total = total + this.derived_data[i];
    end
    return total;
  endfunction

  // Test foreach accessing both arrays
  function int total_sum();
    int total = 0;
    foreach (this.base_data[i]) begin
      total = total + this.base_data[i];
    end
    foreach (this.derived_data[j]) begin
      total = total + this.derived_data[j];
    end
    return total;
  endfunction
endclass

module test;
  DerivedContainer c;
  int result;

  initial begin
    c = new();

    // Test base class sum (100 + 101 + 102 = 303)
    result = c.base_sum();
    if (result != 303) begin
      $display("FAILED: base_sum() returned %0d, expected 303", result);
      $finish;
    end

    // Test derived class sum (0 + 10 + 20 + 30 = 60)
    result = c.derived_sum();
    if (result != 60) begin
      $display("FAILED: derived_sum() returned %0d, expected 60", result);
      $finish;
    end

    // Test total sum (303 + 60 = 363)
    result = c.total_sum();
    if (result != 363) begin
      $display("FAILED: total_sum() returned %0d, expected 363", result);
      $finish;
    end

    $display("PASSED");
  end
endmodule
