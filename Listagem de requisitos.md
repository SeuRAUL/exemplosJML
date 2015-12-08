    Número de Classes

    Quantidade de Métodos

    Herança e Interface

        public interface Age {
            //@ model instance int age;
        }

        public interface NormalSetAge implements Age {
            /*@ requires 0 <= a && a <= 150;
            @ assignable age;
            @ ensures age == a;
            @*/
            public void setAge(int a);
        }


        public interface ExceptionalSetAge implements Age {
            /*@ requires a < 0;
            @ assignable \nothing;
            @ ensures age == \old(age);
            @*/
            public void setAge(int a);
        }


    LOC

    invariant

        public class ArrayOps {
            private /*@ spec_public @*/ Object[] a;

            #//@ public invariant 0 < a.length;#

            /*@ requires 0 < arr.length;
            @ ensures this.a == arr;
            @*/

            public void init(Object[] arr) {
                this.a = arr;
            }
        }

    initially

    constraint

    assignable

    requires

    ensures

    behaviour (normal and exceptional)

    \forall

    \exists

    Modelos (represents)

    behaviour subtyping