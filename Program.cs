using System;
using System.Collections.Generic;
using System.Text;

namespace mangolian
{
    struct Pair<A, B>
    {
        public A fst;
        public B snd;

        public Pair(A x, B y) { fst = x; snd = y; }
    }

    struct Unit {}

    delegate Thunk Thunk();

    delegate Thunk Kont<T>(T x);

    class Res<T> : Exception
    {
        public T res;
        public Res(T x) { res = x; }
    }

    class Program
    {
        static Pair<A, B> pair<A, B>(A a, B b)
        {
            Pair<A, B> p;
            p.fst = a; p.snd = b;
            return p;
        }

        static Unit unit; //() { Unit u; return u; }

        static Thunk run<T>(Kont<T> f, T x)
        {
            return f(x);
        }

        static void Main(string[] args)
        {

            Thunk fmain = () => run<Kont<Pair<Kont<Kont<int>>, Kont<Kont<Pair<Kont<Kont<int>>, 
                Kont<int>>>>>>>(x2 => () => run<Pair<Kont<Kont<int>>, Kont<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>>>
                    (x2, pair<Kont<Kont<int>>, Kont<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>>(k3 => () => run<int>(k3, 5), 
                    x0 => () => run<Pair<Kont<Kont<int>>, Kont<int>>>(x0, pair<Kont<Kont<int>>, Kont<int>>
                        (k1 => () => run<int>(k1, 3), x => { throw new Res<int>(x); })))), w4 => () => 
                            run<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>(w4.snd, w5 => () => run<Kont<int>>(w4.fst, 
                                a6 => () => run<Kont<int>>(w5.fst, b7 => () => run<int>(w5.snd, (a6 + b7))))));
            try
            {
                while (true)
                {
                    fmain = fmain();
                }
            }
            catch (Res<int> r)
            {
                Console.WriteLine("result: {0}", r.res);
            }

        }//main
    }
}
