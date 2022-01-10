class MineTest5 {
  static int randInt;
  static int a;

  static void main() {
    randInt = iiscPavUtil.random();
    if (randInt == 1) {
      a = 1;
      foo();
    }
  }

  static void foo() {
    if (a == 1) {
      a = a + 1;
      return;
    } else {
      a = a + 1;
      return;
    }
  }
}
