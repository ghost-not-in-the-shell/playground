open Array

(* page 31 *)
let merge _A p q r =
  let _L = sub _A    p  (1+q-p) in
  let _R = sub _A (1+q) (  r-q) in
  let i  = ref 0                in
  let j  = ref 0                in
  for k = p to r do
    if !j = length _R ||
       !i < length _L &&
       _L.(!i) < _R.(!j)
    then begin _A.(k) <- _L.(!i); incr i end
    else begin _A.(k) <- _R.(!j); incr j end
  done

(* page 34 *)
let rec merge_sort _A p r =
  if p < r
  then begin
    let q = (p + r) / 2 in
    merge_sort _A p     q;
    merge_sort _A (q+1) r;
    merge _A p q r
  end

let sort _A = merge_sort _A 0 (length _A - 1)
