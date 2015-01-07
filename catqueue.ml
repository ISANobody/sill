open Base
open Core.Std

(* Based Heavily off the Jane Street SLinked_queue implementation. This module provides a thread
   safe queue with the ability to concatenate two queues together. I'd like have done this
   as just an extra function on squeue, but it doesn't expose its mutex. *)

let concat_lock = Mutex.create ()

let thread_print _ = () (* Mutex.synchronize print_endline *)

(* This seems like a very bad idea *)
let broadcast_all l = List.iter l Condition.broadcast

type 'a t = { 
  q: [ `Q of 'a Linked_queue.t | `I of 'a t] ref;
  mutex: Mutex.t;
  not_empty: Condition.t;
  broadlist: Condition.t list ref;
}

let create () : 'a t = 
     let ne = (Condition.create ())
     in
     { q = ref (`Q (Linked_queue.create ()));
       mutex = Mutex.create ();
       not_empty = ne;
       broadlist = ref [ne];
     }

(* Not synchronized *)
let rec is_empty (q: 'a t) : bool =
  match !(q.q) with
  | `Q que -> Linked_queue.is_empty que
  | `I q' -> is_empty q'

let rec push (q: 'a t) (x: 'a) : unit =
  Mutex.lock q.mutex;
  match !(q.q) with
  | `Q que -> Linked_queue.enqueue que x;
              broadcast_all !(q.broadlist);
              Mutex.unlock q.mutex
  | `I q' -> Mutex.unlock q.mutex;
             push q' x

(* This isn't as efficient, it gives a modified busy wait,
   but what I thought was standard condition variable usage
   gave errors I can't figure out.
   Precondition: qmu is held
   Postcondition: !(q.mutex) is held and length q > 0 *)
let rec wait_not_empty (q: 'a t): 'a t =
  match !(q.q) with
  | `Q que -> if Linked_queue.is_empty que
              then (Condition.wait q.not_empty q.mutex;
                    wait_not_empty q)
              else q
  | `I q' -> Mutex.unlock q.mutex;
             Mutex.lock q'.mutex;
             wait_not_empty q'

(* We shouldn't busy wait here *)
let rec pop (q: 'a t) : 'a =
  Mutex.lock q.mutex;
  let q' = wait_not_empty q
  in match !(q'.q) with
     | `Q que -> let r = Linked_queue.dequeue_exn que;
                 in broadcast_all !(q'.broadlist);
                    assert (Linked_queue.length que < 2);
                    Mutex.unlock q'.mutex;
                    r
     | `I _ -> failwith "wait_not_empty returned an indirection"
             


(* Taking two locks makes me nervous here.
   Unfortunately, doing concat q1 q2 while some other thread
   does concat q2 q3 is tricky. q2 ends up being the residual one *)
let rec concat (q1: 'a t) (q2: 'a t) : unit =
  assert (not (physeq q1 q2));
  Mutex.lock q1.mutex;
  Mutex.lock q2.mutex;
  match !(q1.q) with
  | `I q' -> Mutex.unlock q2.mutex;
             Mutex.unlock q1.mutex;
             concat q' q2
  | `Q que1 -> 
    match !(q2.q) with
    | `I q' -> Mutex.unlock q2.mutex;
               Mutex.unlock q1.mutex;
               concat q1 q'
    | `Q que2 -> (* assert (Linked_queue.length que1 + Linked_queue.length que2 < 2); *)
                 Linked_queue.transfer que1 que2;
                 assert (Linked_queue.is_empty que1);
                 q1.q := `I q2;
                 q2.broadlist := !(q1.broadlist) @ !(q2.broadlist);
                 broadcast_all !(q2.broadlist);
                 Mutex.unlock q1.mutex;
                 Mutex.unlock q2.mutex
