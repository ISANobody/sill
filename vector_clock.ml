open Base
open Core.Std

module VectorClock =
struct
  type t = (int list,int) Map.Poly.t
  let create id = Map.Poly.singleton id 0
  let merge local remote id = 
     let ret = Map.Poly.merge local remote ~f:(fun ~key:k -> 
               function 
               | `Left i -> Some i
               | `Right i -> Some i
               | `Both (l,r) -> Some (max l r))
     in let maax = Map.Poly.fold ret ~init:0 ~f:(fun ~key:k ~data:t acc -> max acc t)
        in Map.Poly.add ret id (maax+1)
  let merge1 local remote id = local := merge !local remote id
  let incr local id = Map.Poly.change local id 
      (function
      | None -> Some 0
      | Some i -> Some (i+1))
  let incr1 local id = local := incr !local id
  let get local id = Map.Poly.find_exn local id
  let get1 local id = Map.Poly.find_exn !local id
end
