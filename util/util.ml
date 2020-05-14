let new_var =
  let v = ref 0
  in
  function () ->
    begin
      incr v;
      if (!v <0) then failwith "No more free variables available. You exhaust me !!";
      !v
    end;;
