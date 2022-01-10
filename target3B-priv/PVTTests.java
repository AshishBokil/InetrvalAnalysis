class PVTTests
{
    static void pvttest1() {
        int i = -5;
        int j = -10;
        while(i < 100 && j < 80) {
            if (j >= i) {
            }
            i = i + 1;
            j = j + 2;
        }
    }

    static void pvttest2() {
        int i = -2;
        while (-20 < i) {
            i = i - 1;
        }
    }

    public static void main(String args[])
    {
        pvttest1();
    }
}

