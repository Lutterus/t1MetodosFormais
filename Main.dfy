class Queue
{
    var queue: array<int>;

    constructor ()
        ensures queue.Length == 0
    {
        queue := new int[0];
    }

    method isEmpty() returns (boolean:bool)
    ensures (queue.Length == 0 && boolean == true) || (queue.Length > 0 && boolean == false)
    {
        if(queue.Length == 0) {
            boolean := true;
        } else {
            boolean := false;
        }
        return boolean;
    }

    method size() returns (size:nat)
    ensures size == queue.Length
    {
        return queue.Length;
    }

    method get() returns (num:int)
        requires queue.Length > 0
        ensures num == queue[0]
    {
        return queue[0];
    }

    method add(newNumber:nat)
        modifies this
        ensures queue.Length == old(queue.Length + 1)
        ensures queue[0] == newNumber
    {
        var newQueue := new int[queue.Length + 1];
        newQueue[0] := newNumber;

        forall i | 1 <= i < newQueue.Length { 
            newQueue[i] := queue[i - 1];
        }

        queue := newQueue;
    }

    method pop()
        modifies this
        requires queue.Length > 1
        ensures queue.Length == old(queue.Length - 1)
        ensures queue[0] == old(queue[1])
        // ensures forall k :: 0 <= k < queue.Length ==> queue[k] == old(queue[k+1])
    {
        var newQueue := new int[queue.Length - 1];
        forall i | 0 <= i < newQueue.Length { 
            newQueue[i] := queue[i + 1];
        }
        queue := newQueue;
    }

    method invert()
        modifies this
        requires queue.Length > 0
        ensures queue.Length == old(queue.Length)
        // ensures forall k :: 0 <= k < queue.Length ==> queue[k] == old(queue[queue.Length - (k+1)])
        // ensures queue[queue.Length - 1] == old(queue[0]) && queue[0] == old(queue[queue.Length - 1])
        // ensures forall k | 0 <= k < i :: queue[k] == old(queue[queue.Length-1-k])
    {
        var newQueue := new int[queue.Length];
        forall i | 1 <= i < queue.Length
        { 
            newQueue[i] := queue[queue.Length - (i + 1)];
        }
        queue := newQueue;
        // forall k | 0 <= k < i :: newQueue[k] == queue[queue.Length-1-k];
    }
}

method Main()
{
    // Intanciação
    var queue := new Queue();

    // Confirma que esta vazio
    var isEmpty := queue.isEmpty();
    var size := queue.size();
    assert size == 0;
    assert isEmpty == true;
    
    // Add
    queue.add(2);

    // Confirma que nao esta mais vazio
    isEmpty := queue.isEmpty();
    size := queue.size();
    assert size == 1;
    assert isEmpty == false;

    // Confirma o numero no topo da pilha
    var num := queue.get();
    assert num == 2;

    // Add
    queue.add(5);
    // Confirma o numero no topo da pilha
    num := queue.get();
    assert num == 5;
    size := queue.size();
    assert size == 2;

    // Remove elemento
    queue.pop();
    // Confirma o numero no topo da pilha
    size := queue.size();
    assert size == 1;
    num := queue.get();
    assert num == 2;


    // // Confirma que a pilha esta vazia
    // queue.pop();
    // isEmpty := queue.isEmpty();
    // size := queue.size();
    // assert size == 0;
    // assert isEmpty == true;

    // // Add
    // queue.add(8);
    // queue.add(9);
    // queue.add(12);

    // // Confirma que a pilha foi invertida
    // num := queue.get();
    // assert num == 12;
    // queue.invert();
    // num := queue.get();
    // assert num == 8;
}