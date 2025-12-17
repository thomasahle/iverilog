// Test structural equivalence for unpacked structs
// This tests that typedef'd structs defined in different scopes
// but with the same structure are considered equivalent.

module test;

  // Define struct type in one scope
  typedef struct {
    logic [7:0] a;
    logic [15:0] b;
    int c;
  } mystruct_t;

  // Function that takes mystruct_t
  function automatic void print_struct(mystruct_t s);
    $display("Struct: a=%h, b=%h, c=%0d", s.a, s.b, s.c);
  endfunction

  // Class that uses the struct
  class myclass;
    // Define a LOCAL struct with same structure but different typedef
    typedef struct {
      logic [7:0] a;
      logic [15:0] b;
      int c;
    } local_struct_t;

    local_struct_t data;

    function new();
      data.a = 8'hAB;
      data.b = 16'hCDEF;
      data.c = 42;
    endfunction

    // Try to pass local_struct_t to a function expecting mystruct_t
    // This should work if structural equivalence is implemented
    function void show();
      mystruct_t temp;
      temp = data;  // Assignment between equivalent struct types
      print_struct(temp);
    endfunction
  endclass

  initial begin
    mystruct_t s1;
    myclass obj;

    s1.a = 8'h11;
    s1.b = 16'h2233;
    s1.c = 100;

    $display("Testing struct type equivalence...");
    print_struct(s1);

    obj = new();
    obj.show();

    // Test direct assignment
    s1 = obj.data;
    $display("After assignment from class struct:");
    print_struct(s1);

    $display("PASSED");
  end

endmodule
