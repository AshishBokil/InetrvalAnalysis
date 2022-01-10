class MineTest7 {
    static int randInt;
    static int a;

    static void main() {
        randInt = iiscPavUtil.random();
        if (randInt == 1) {
            a = 1;
            MineTest7_2.foo();
        }
    }
}

class MineTest7_2 {
    static int a = 10;

    static void foo() {

        while (a < 10) {
            MineTest7.a = MineTest7.a + 1;

        }
        return;
    }

}