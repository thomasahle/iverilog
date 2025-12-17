// Test enum.name() method on class properties
module test;
  typedef enum {IDLE, READ, WRITE, DONE} state_e;

  class MyClass;
    state_e state;

    function string get_state_name();
      return state.name();
    endfunction
  endclass

  initial begin
    MyClass obj = new();

    obj.state = IDLE;
    if (obj.state.name() != "IDLE") begin
      $display("FAILED: Expected IDLE, got %s", obj.state.name());
      $finish;
    end

    obj.state = READ;
    if (obj.get_state_name() != "READ") begin
      $display("FAILED: Expected READ, got %s", obj.get_state_name());
      $finish;
    end

    obj.state = WRITE;
    if (obj.state.name() != "WRITE") begin
      $display("FAILED: Expected WRITE, got %s", obj.state.name());
      $finish;
    end

    obj.state = DONE;
    if (obj.get_state_name() != "DONE") begin
      $display("FAILED: Expected DONE, got %s", obj.get_state_name());
      $finish;
    end

    $display("PASSED");
  end
endmodule
