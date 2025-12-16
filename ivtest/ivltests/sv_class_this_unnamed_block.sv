// Test for 'this' lookup in unnamed blocks within class methods
// This tests the fix for finding 'this' when inside unnamed blocks
// created by macro expansions or other constructs

`define MY_INFO(msg) \
  begin \
    $display("[%s] %s", this.get_name(), msg); \
  end

class MyClass;
  string m_name;
  int m_value;

  function new(string name);
    m_name = name;
    m_value = 0;
  endfunction

  function string get_name();
    return m_name;
  endfunction

  function void set_value(int v);
    m_value = v;
  endfunction

  function int get_value();
    return m_value;
  endfunction

  // Test 'this' access from within an unnamed block
  task run();
    `MY_INFO("Starting run")

    // Nested unnamed block
    begin
      `MY_INFO("In nested block")
      this.set_value(42);
    end

    // Another level of nesting
    begin
      begin
        `MY_INFO("In deeply nested block")
        if (this.get_value() == 42) begin
          `MY_INFO("Value check passed")
        end
      end
    end

    `MY_INFO("Ending run")
  endtask

  // Test 'this' in forever block (like UVM run_phase)
  task run_forever();
    int count = 0;
    forever begin
      `MY_INFO($sformatf("Iteration %0d", count))
      this.set_value(count);
      count++;
      if (count >= 3) break;
    end
  endtask
endclass

module test;
  initial begin
    MyClass obj = new("test_obj");

    obj.run();

    if (obj.get_value() != 42) begin
      $display("FAILED: Expected value 42, got %0d", obj.get_value());
      $finish;
    end

    obj.run_forever();

    if (obj.get_value() != 2) begin
      $display("FAILED: Expected value 2, got %0d", obj.get_value());
      $finish;
    end

    $display("PASSED");
  end
endmodule
