class MineTest6 {
    static int randInt;
    static int a;

    static void main() {
        randInt = iiscPavUtil.random();
        if (randInt == 1) {
            a = 1;
            MineTest6_2.foo();
        }
    }
}

class MineTest6_2 {

    static void foo() {
        if (MineTest6.a == 1) {
            MineTest6.a = MineTest6.a + 1;
            return;
        } else {
            MineTest6.a = MineTest6.a + 1;
            return;
        }
    }

}