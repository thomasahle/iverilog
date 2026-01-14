// BUG DOCUMENTATION: Parameterized class with real type parameter crashes
// 
// When a parameterized class uses T=real, the VVP runtime crashes with:
//   Assertion failed: (0), function set_vec4, file class_type.cc, line 127
//
// This is a pre-existing bug in the VVP runtime, not related to grammar parsing.
// The parsing works correctly - the crash occurs at runtime when the property
// with real type is assigned.
//
// Root cause (suspected): class_type.cc set_vec4() doesn't handle real type
// properties correctly - real values should use set_real() not set_vec4().
//
// Workaround: Use wrapper classes instead of real type parameter:
//   class RealWrapper { real value; }
//   Container#(RealWrapper) c;  // Works
//   Container#(real) c;         // Crashes

package my_pkg;
  class Container #(type T = int);
    T data;
    function new();
    endfunction
    function void set(T val);
      data = val;
    endfunction
    function T get();
      return data;
    endfunction
  endclass
endpackage

module test;
  import my_pkg::*;

  // This will crash at runtime with:
  //   Assertion failed: (0), function set_vec4, file class_type.cc, line 127
  my_pkg::Container#(real) c_real;

  initial begin
    c_real = new();
    c_real.set(3.14);  // Crash happens here
    
    if (c_real.get() == 3.14)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
