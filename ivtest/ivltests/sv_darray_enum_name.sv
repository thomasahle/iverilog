// Test enum .name() method on dynamic array elements that are class properties
// Pattern: obj.enum_darray[i].name()

module test;
  typedef enum logic [1:0] {
    IDLE   = 2'b00,
    READ   = 2'b01,
    WRITE  = 2'b10,
    ERROR  = 2'b11
  } operation_e;

  class Container;
    operation_e ops[];

    function new();
      ops = new[4];
      ops[0] = IDLE;
      ops[1] = READ;
      ops[2] = WRITE;
      ops[3] = ERROR;
    endfunction
  endclass

  Container c;
  int pass = 1;

  initial begin
    c = new();

    // Test .name() on class property darray elements
    if (c.ops[0].name() != "IDLE") begin
      $display("FAILED: c.ops[0].name() = %s, expected IDLE", c.ops[0].name());
      pass = 0;
    end

    if (c.ops[1].name() != "READ") begin
      $display("FAILED: c.ops[1].name() = %s, expected READ", c.ops[1].name());
      pass = 0;
    end

    if (c.ops[2].name() != "WRITE") begin
      $display("FAILED: c.ops[2].name() = %s, expected WRITE", c.ops[2].name());
      pass = 0;
    end

    if (c.ops[3].name() != "ERROR") begin
      $display("FAILED: c.ops[3].name() = %s, expected ERROR", c.ops[3].name());
      pass = 0;
    end

    // Test with variable index in foreach loop
    foreach (c.ops[i]) begin
      case (i)
        0: if (c.ops[i].name() != "IDLE") begin $display("FAILED: loop i=%0d", i); pass = 0; end
        1: if (c.ops[i].name() != "READ") begin $display("FAILED: loop i=%0d", i); pass = 0; end
        2: if (c.ops[i].name() != "WRITE") begin $display("FAILED: loop i=%0d", i); pass = 0; end
        3: if (c.ops[i].name() != "ERROR") begin $display("FAILED: loop i=%0d", i); pass = 0; end
      endcase
    end

    if (pass)
      $display("PASSED");
  end
endmodule
