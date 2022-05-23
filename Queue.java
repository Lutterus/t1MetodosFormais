public class Queue {
    int[] queue = new int[0];

    public Queue() {

    }

    public void print() {
        String text = "";
        for (int i = 0; i < queue.length; i++) {
            text += Integer.toString(queue[i]) + ", ";
        }
        System.out.println(text);
    }

    public void add(int newNumber) {
        int[] newQueue = new int[queue.length + 1];
        newQueue[0] = newNumber;

        for (int i = 1; i < newQueue.length; i++) {
            newQueue[i] = queue[i - 1];
        }
        queue = newQueue;
    }

    public void pop() {
        if (queue.length == 0) {
            return;
        }

        int[] newQueue = new int[queue.length - 1];
        for (int i = 0; i < newQueue.length; i++) {
            newQueue[i] = queue[i + 1];
        }
        queue = newQueue;
    }

    public int get() throws Exception {
        if (queue.length == 0) {
            throw new Exception("Fila vazia");
        }
        return queue[0];
    }

    public boolean isEmpty() {
        if (queue.length == 0) {
            return true;
        }
        return false;
    }

    public int size() {
        return queue.length;
    }

    public void invert() {
        int[] newQueue = new int[queue.length];

        for (int i = 0; i < queue.length; i++) {
            newQueue[i] = queue[queue.length - (i + 1)];
        }

        boolean bol = newQueue.length == 0 || newQueue[0] == queue[queue.length - 1];
        
        queue = newQueue;
    }
}
