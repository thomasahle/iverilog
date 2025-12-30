// Test that parameterized class specializations are properly shared
// across different scopes to avoid duplicate class definitions in VVP

package pkg;
  class holder #(type T = int);
    T data;
    function new();
      data = T'(0);
    endfunction
  endclass
endpackage

import pkg::*;

class user1;
  holder #(int) h1;
  function void run();
    h1 = new();
    h1.data = 42;
    $display("user1: h1.data = %0d", h1.data);
  endfunction
endclass

class user2;
  holder #(int) h2;  // Same specialization as user1 - should share class def
  function void run();
    h2 = new();
    h2.data = 100;
    $display("user2: h2.data = %0d", h2.data);
  endfunction
endclass

module top;
  user1 u1;
  user2 u2;

  initial begin
    u1 = new();
    u2 = new();
    u1.run();
    u2.run();
    #1;
    $display("PASSED");
    $finish;
  end
endmodule
