public class Main {
    public static void main(String[] args) throws Exception {
        Queue queue = new Queue();

        boolean isEmpty = queue.isEmpty();
        System.out.println("isEmpty:" + isEmpty);

        int size = queue.size();
        System.out.println("size: " + size);

        queue.add(2);
        queue.add(4);
        queue.add(5);
        queue.print();

        queue.pop();
        queue.print();

        int num = queue.get();
        System.out.println("num: " + num);

        isEmpty = queue.isEmpty();
        System.out.println("isEmpty: " + isEmpty);

        size = queue.size();
        System.out.println("size: " + size);

        queue.add(8);
        queue.add(12);
        System.out.println("antes de inverter: ");
        queue.print();

        queue.invert();
        System.out.println("depois de inverter: ");
        queue.print();
        
        queue.pop();
        queue.invert();
        queue.print();

        queue.pop();
        queue.invert();
        queue.print();

        queue.pop();
        queue.invert();
        queue.print();

        queue.pop();
        queue.invert();
        queue.print();

        queue.pop();
        queue.invert();
        queue.print();

        // invariant -1 <= index <= queue.Length

    }
}