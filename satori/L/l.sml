signature STACKS =
sig
      type 'a stacks
      val snil : 'a stacks (* Tworzy zestaw 6-ciu stosów o numerach 0, 1, 2, 3, 4, 5 *)
      val size : int -> 'a stacks -> int (* Zwraca rozmiar stosu o podanym numerze - O(1) *)
      val empty : int -> 'a stacks -> bool (* Sprawdza, czy stos jest niepusty *)

      val pop : int -> 'a stacks -> 'a stacks (* Usuwa element na szczycie stosu *)
      val copy : int -> int -> 'a stacks -> 'a stacks (* Kopiuje element znajdujący się na szczycie pierwszego stosu na drugi stos *)
      val dup : int -> int -> 'a stacks -> 'a stacks (*  Kopiuje cały pierwszy stos na drugi stos. Poprzednia zawartość drugiego stosu jest tracona *)
      val clear : int -> 'a stacks -> 'a stacks (* Czyści stos o podanym numerze *)
      val get_stack : int -> 'a stacks -> 'a list;
end

signature RQUEUE =
sig
      type 'a info
      type 'a stacks
      val qnil : 'a stacks * 'a info (* Tworzenie pustej kolejki *)
      val enq : int stacks * 'a info -> int stacks * 'a info (* Dodawanie elementu na koniec kolejki *)
      val deq : int stacks * 'a info -> int stacks * 'a info (* Pobieranie i usuwanie elementu na początku kolejki *)
end

structure SixStacks : STACKS =
struct
      type 'a stacks = (int * 'a list) list
      val snil = [(0, []), (0, []), (0, []), (0, []), (0, []), (0, [])]
      fun pop 0 ((cnt, head::tail)::rest) = (cnt-1, tail) :: rest
        | pop n (head::tail) = head :: (pop (n-1) tail)
      fun empty 0 ((cnt, _)::_) = cnt = 0
        | empty n (_::tail) = empty (n-1) tail
      local
              fun get 0 ((_, h::_)::_) = h
                | get n (_::tail) = get (n-1) tail
              fun put 0 v ((cnt, t)::rest) = (cnt+1, v::t)::rest
                | put n v (head::tail) = head :: (put (n-1) v tail)
      in
              fun copy i j S = put j (get i S) S
      end
      fun dup i j S = List.take (S, j) @ (List.nth (S, i) :: List.drop (S, j+1))
      fun clear i S = List.take (S, i) @ ((0, []) :: List.drop (S, i+1))
      fun size i (S : 'a stacks) = #1 (List.nth (S, i))
      
      fun get_stack (i: int) (S: 'a stacks) : 'a list = #2(List.nth (S,i));
end
