class MineTest8 {
    static int randInt;
    static int a;

    static void main() {
        randInt = iiscPavUtil.random();
        if (randInt == 1) {
            a = 1;
            MineTest8_2.foo();
        }
    }
}

class MineTest8_2 {
    static int a = 10;

    static void foo() {

    }

    void rec() {
        if (MineTest8.a < a) {
            MineTest8.a = MineTest8.a + 1;
            rec();
        }
    }

}