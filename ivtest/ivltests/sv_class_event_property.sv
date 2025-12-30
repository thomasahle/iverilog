// Test event as class property
// Events in classes can be declared and used for synchronization

module test;

class EventHandler;
  event myEvent;
  int count;

  function new();
    count = 0;
  endfunction

  task trigger_event();
    count++;
    ->myEvent;  // Trigger the event
  endtask

  task wait_for_event();
    @myEvent;
  endtask
endclass

EventHandler handler;

initial begin
  handler = new();

  // Fork a process to wait for the event
  fork
    begin
      handler.wait_for_event();
      $display("Event received, count = %0d", handler.count);
    end
    begin
      #10;
      handler.trigger_event();
    end
  join

  if (handler.count == 1)
    $display("PASSED");
  else
    $display("FAILED - count = %0d", handler.count);
end

endmodule
