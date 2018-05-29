open Array

(* page 15 *)
let insert _A j =
  let key = _A.(j)    in
  let i   = ref (j-1) in
  while !i >= 0 && _A.(!i) > key do
    _A.(!i+1) <- _A.(!i);
    decr i
  done;
  _A.(!i+1) <- key

let sort _A =
  for j = 1 to length _A - 1 do
    insert _A j
  done
