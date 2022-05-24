class {:autocontracts} Queue
{
    var queue: array<int>;
    ghost var queueAbs: seq<nat>;
    ghost var queueSizeAbs: int;

    predicate Valid()
    {
        queueSizeAbs == queue.Length &&
        (
            (queueSizeAbs == 0 && queueAbs == []) ||
            queueAbs == queue[0..queueSizeAbs]
        )
    }

    constructor ()
        ensures queue.Length == 0
        ensures queueAbs == []
        ensures queueSizeAbs == queue.Length;
    {
        queue := new int[0];
        queueAbs := [];
        queueSizeAbs := 0;
    }

    method isEmpty() returns (boolean:bool)
        ensures (queueSizeAbs == 0 && boolean == true) || (queueSizeAbs > 0 && boolean == false)
        ensures Valid()
    {
        if(queue.Length == 0) {
            boolean := true;
        } else {
            boolean := false;
        }
        
        return boolean;
    }

    method size() returns (size:int)
        ensures size == queueSizeAbs
    {
        size := queue.Length;
        return size;
    }

    method get() returns (num:int)
        requires queueSizeAbs > 0
        ensures num == queueAbs[0]
    {
        return queue[0];
    }

    method add(newNumber:nat)
        ensures queueSizeAbs == old(queueSizeAbs + 1)
        ensures queueAbs[0] == newNumber
        ensures queueAbs == [newNumber] + old(queueAbs)
        // ensures forall k :: 1 <= k < queueSizeAbs ==> queue[k] == old(queue[k-1])
    {
        var newQueue := new int[queue.Length + 1];
        newQueue[0] := newNumber;

        forall i | 1 <= i < queue.Length + 1 { 
            newQueue[i] := queue[i - 1];
        }

        queue := newQueue;
        // Atualiza ghosts
        queueAbs := [newNumber] + queueAbs;
        queueSizeAbs := queueSizeAbs + 1;
    }

    method pop()
        requires queueSizeAbs > 0
        ensures (queueSizeAbs >= 0 && queueSizeAbs == old(queueSizeAbs - 1))
        ensures queueAbs == old(queueAbs)[1..]
        // ensures forall k :: 0 <= k < queueSizeAbs ==> queue[k] == old(queue[k+1])
    {
        var newQueue := new int[queue.Length - 1];
        forall i | 0 <= i < queue.Length - 1 { 
            newQueue[i] := queue[i + 1];
        }
        queue := newQueue;
        // Atualiza ghosts
        queueAbs := queue[0..queue.Length];
        queueSizeAbs := queueSizeAbs - 1;
    }

    method invert()
        ensures queueSizeAbs == old(queueSizeAbs)
        ensures forall k :: 0 <= k < queueSizeAbs ==> queueAbs[k] == old(queueAbs[queueSizeAbs - (k+1)])
    {
        var newQueue := new int[queue.Length];
        forall i | 0 <= i < queue.Length
        { 
            newQueue[i] := queue[queue.Length - (i + 1)];
        }
        queue := newQueue;
        // Atualiza ghosts
        queueAbs := queue[0..queue.Length];
        queueSizeAbs := queue.Length;
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
    queue.add(5);

    // Confirma que nao esta mais vazio
    isEmpty := queue.isEmpty();
    size := queue.size();
    assert size == 1;
    assert isEmpty == false;

    // Confirma o numero no topo da pilha
    var num := queue.get();
    assert num == 5;

    // Add
    queue.add(6);
    // Confirma o numero no topo da pilha
    num := queue.get();
    assert num == 6;
    // Confirma novo tamanho
    size := queue.size();
    assert size == 2;

    // Remove elemento
    queue.pop();
    // Confirma novo tamanho
    size := queue.size();
    assert size == 1;
    // Confirma numero no topo da pilha
    num := queue.get();
    assert num == 5;


    // Confirma que a pilha esta vazia
    queue.pop();
    isEmpty := queue.isEmpty();
    size := queue.size();
    assert size == 0;
    assert isEmpty == true;

    // Add
    queue.add(8);
    queue.add(9);
    queue.add(12);

    // Confirma o reeprenchimento da pilha
    size := queue.size();
    assert size == 3;
    num := queue.get();
    assert num == 12;

    // Inverte a pilha inteira
    queue.invert();
    // Confirma que a pilha foi invertida
    num := queue.get();
    assert num == 8;

    // Confirma o tamanho
    isEmpty := queue.isEmpty();
    size := queue.size();
    assert size == 3;
    assert isEmpty == false;

    // Esvazia a fila
    queue.pop();
    queue.pop();
    queue.pop();

    // Confirma que esta vazio
    isEmpty := queue.isEmpty();
    size := queue.size();
    assert size == 0;
    assert isEmpty == true;
}