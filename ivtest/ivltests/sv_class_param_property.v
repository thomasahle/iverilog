// Test for parameterized class used as a class property
// This tests that parameterized classes can be used as properties
// in other parameterized classes

class Container #(type T = int);
  T m_data;
  string m_name;

  function new(string name);
    m_name = name;
  endfunction

  function void set_data(T data);
    m_data = data;
  endfunction

  function T get_data();
    return m_data;
  endfunction

  function string get_name();
    return m_name;
  endfunction
endclass

class Wrapper #(type T = int);
  // Parameterized class as a property
  Container #(T) m_container;
  string m_wrapper_name;

  function new(string name);
    m_wrapper_name = name;
    m_container = new("inner_container");
  endfunction

  function void store(T value);
    m_container.set_data(value);
  endfunction

  function T retrieve();
    return m_container.get_data();
  endfunction

  function string describe();
    return {m_wrapper_name, " contains ", m_container.get_name()};
  endfunction
endclass

module test;
  initial begin
    Wrapper #(int) int_wrapper;
    Wrapper #(bit [7:0]) byte_wrapper;

    // Test int wrapper
    int_wrapper = new("int_wrap");
    int_wrapper.store(42);
    if (int_wrapper.retrieve() != 42) begin
      $display("FAILED: int_wrapper.retrieve() = %0d, expected 42", int_wrapper.retrieve());
      $finish;
    end

    // Test description
    if (int_wrapper.describe() != "int_wrap contains inner_container") begin
      $display("FAILED: describe() = '%s'", int_wrapper.describe());
      $finish;
    end

    // Test byte wrapper
    byte_wrapper = new("byte_wrap");
    byte_wrapper.store(8'hAB);
    if (byte_wrapper.retrieve() != 8'hAB) begin
      $display("FAILED: byte_wrapper.retrieve() = %0h, expected AB", byte_wrapper.retrieve());
      $finish;
    end

    $display("PASSED");
  end
endmodule
