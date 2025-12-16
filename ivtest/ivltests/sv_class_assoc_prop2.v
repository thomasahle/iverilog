// Test associative array class property indexing with implicit this
// Tests both write (l-value) and read (r-value) access without explicit this

module test;
  class DataStore;
    int data[int];  // Int-keyed associative array

    function void store(int key, int value);
      data[key] = value;  // Implicit this - l-value
    endfunction

    function int load(int key);
      return data[key];  // Implicit this - r-value
    endfunction

    function void update(int key, int delta);
      data[key] = data[key] + delta;  // Both read and write with implicit this
    endfunction
  endclass

  DataStore ds;
  int val;

  initial begin
    ds = new();

    // Store some values
    ds.store(100, 42);
    ds.store(200, 84);
    ds.store(300, 126);

    // Check loaded values
    val = ds.load(100);
    if (val !== 42) begin
      $display("FAILED: load(100) = %0d, expected 42", val);
      $finish;
    end

    val = ds.load(200);
    if (val !== 84) begin
      $display("FAILED: load(200) = %0d, expected 84", val);
      $finish;
    end

    // Test update (read + write in same expression)
    ds.update(100, 10);
    val = ds.load(100);
    if (val !== 52) begin
      $display("FAILED: after update, load(100) = %0d, expected 52", val);
      $finish;
    end

    $display("PASSED");
  end
endmodule
