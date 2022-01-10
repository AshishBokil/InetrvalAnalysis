class MineTest9 {
    static int randInt;
    static int a;

    static void main() {
        randInt = iiscPavUtil.random();
        if (randInt == 1) {
            a = 1;
            MineTest9_2.foo();
        }
    }
}

class MineTest9_2 {
    static int a = 10;

    static void foo() {

    }

    void rec1() {
        if (MineTest9.a < a) {
            MineTest9.a = MineTest9.a + 1;
            rec2();
        }
    }

    void rec2() {
        if (MineTest9.a < a) {
            MineTest9.a = MineTest9.a + 1;
            rec1();
        }
    }

}