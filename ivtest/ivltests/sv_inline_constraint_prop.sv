// Test inline constraint referencing class properties
//
// Demonstrates that inline constraints work when they reference
// properties of the same class, but NOT when referencing external variables.
//
// Based on AHB AVIP pattern: req.randomize() with { addr == addrSeq; }
//
// Workaround: Store the constraint values as class properties

class Request;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  // Properties to hold constraint values
  bit [7:0] target_addr;
  bit [7:0] target_data;

  // Named constraint using class properties
  constraint c_target {
    addr == target_addr;
    data == target_data;
  }
endclass

module test;
  initial begin
    Request req;
    int pass = 1;

    req = new();

    // Test 1: Set target values and randomize
    req.target_addr = 8'hAB;
    req.target_data = 8'hCD;

    if (req.randomize()) begin
      if (req.addr != 8'hAB) begin
        $display("FAIL: addr mismatch %h != AB", req.addr);
        pass = 0;
      end
      if (req.data != 8'hCD) begin
        $display("FAIL: data mismatch %h != CD", req.data);
        pass = 0;
      end
    end else begin
      $display("FAIL: randomize failed");
      pass = 0;
    end

    // Test 2: Change target and randomize again
    req.target_addr = 8'h55;
    req.target_data = 8'hAA;

    if (req.randomize()) begin
      if (req.addr != 8'h55) begin
        $display("FAIL: addr mismatch %h != 55", req.addr);
        pass = 0;
      end
      if (req.data != 8'hAA) begin
        $display("FAIL: data mismatch %h != AA", req.data);
        pass = 0;
      end
    end else begin
      $display("FAIL: randomize failed");
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
