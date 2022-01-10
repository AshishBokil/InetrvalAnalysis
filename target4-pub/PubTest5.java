class PubTest5 {
  static int randInt;
  static int a;

  static void main() {
    randInt = iiscPavUtil.random();
    if (randInt == 1) {
      a = 1;
      foo();
    } else {
      a = 2;
      foo();
    }
  }

  static void foo() {
    if (a == 1) {
      bar();
      return;
    } else {
      bar();
      return;
    }
  }

  static void bar() {
    a = a + 1;
  }
}
