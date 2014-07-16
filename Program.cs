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

        class Sum<A, B>
        {
        }

        class Left<A, B> : Sum<A, B>
        {
            public A a;
            public Left(A x) { a = x; }
        }
        class Right<A, B> : Sum<A, B>
        {
            public B b;
            public Right(B x) { b = x; }
        }

        static Sum<A, B> left<A, B>(A a)
        {
            return new Left<A,B>(a);
        }
        static Sum<A, B> right<A, B>(B b)
        {
            return new Right<A, B>(b);
        }

        static Thunk match<A, B>(Sum<A, B> e, Kont<A> fa, Kont<B> fb)
        {
            var l = e as Left<A, B>;
            if (l != null) return () => fa(l.a);
            var r = e as Right<A, B>;
            if (r != null) return () => fb(r.b);
            throw new Exception("bad Sum value");
        }

        static Sum<Unit, Unit> eql(int a, int b)
        {
            if (a == b) return right<Unit, Unit>(unit);
            else return left<Unit, Unit>(unit);
        }

        static Sum<Unit, Unit> less(int a, int b)
        {
            if (a < b) return right<Unit, Unit>(unit);
            else return left<Unit, Unit>(unit);
        }

        static void Main(string[] args)
        {
            Thunk fmain = () => run<int>(a1 => () => run<int>(b2 => () => run<Sum<Unit, Unit>>(z0 => match<Unit, Unit>(z0, l => () => run<int>(x => { throw new Res<int>(x); }, 0), r => () => run<int>(x => { throw new Res<int>(x); }, 1)), less(a1, b2)), 7), 40);
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
