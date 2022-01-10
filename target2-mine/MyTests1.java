class MyTargetClass1 {

    int test1() {
        int sum = 0;
        int y = 1;
        double x = 1.5;
        if (x < 5)
            sum = (int) x + 5;
        else
            sum = sum + y;

        return sum;
    }

    int test2(int y) {

        int x = 5;
        if (y < 5) {
            y = -x;
        }

        return y;
    }

    static int test3(int y, int x) {

        int z = 0;

        if (y < 5) {
            if (x < 10) {
                z = 5;
            } else {
                z = 10;
            }
        } else {
            z = 15;
        }

        return z;
    }

    static int test4() {
        int x = 10;
        int y = 15;
        int sum = 0;
        for (int i = 0; i < y - x; i++) {
            if (i < y) {
                if (i < x) {
                    sum = sum + i;
                }
            }
        }
        return sum;
    }
}

class MyTargetClass2 {
}
