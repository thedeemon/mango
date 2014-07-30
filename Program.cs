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

    delegate Thunk RF<T>(T x, Kont<T> f);

    class UnRec<T>
    {
        RF<T> rf;
        public UnRec(RF<T> recfun) { rf = recfun; }
        public Thunk g(T x)  { return rf(x, g);  }
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

        //delegate Thunk RF<T>(T x, Kont<T> f); (T, T->Th) -> Th
        static Kont<T> unrec<T>(RF<T> rf)
        {
            return new UnRec<T>(rf).g;
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
            Thunk fmain_ = () => run<int>(a3 => () => run<int>(b4 => () => run<Sum<Unit, Unit>>(z2 => match<Unit, Unit>(z2, u0 => () => run<int>(x => { throw new Res<int>(x); }, 20), u1 => () => run<int>(x => { throw new Res<int>(x); }, 1)), less(a3, b4)), 70), 82);
            //RF<int> fff = (int x, Kont<int> f) => { if (x > 200) throw new Res<int>(x); else return run<int>(f, x * 2); };
            //Thunk fmain = () => run<int>(unrec<int>((x, f) => { if (x > 200) throw new Res<int>(x); else return run<int>(f, x * 2); }), 1);
            //Thunk fmain = () => run<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>(x0 => () => run<Pair<Kont<Kont<int>>, Kont<int>>>(x0, pair<Kont<Kont<int>>, Kont<int>>(k1 => () => run<int>(k1, 2), x => { throw new Res<int>(x); })), unrec<Pair<Kont<Kont<int>>, Kont<int>>>((w2, rec3) => () => run<Kont<int>>(w2.fst, a12 => () => run<int>(b13 => () => run<Sum<Unit, Unit>>(z7 => match<Unit, Unit>(z7, u5 => () => run<Kont<int>>(w2.fst, w2.snd), u6 => () => run<Kont<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>>(u4 => () => run<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>(u4, rec3), x8 => () => run<Pair<Kont<Kont<int>>, Kont<int>>>(x8, pair<Kont<Kont<int>>, Kont<int>>(k9 => () => run<Kont<int>>(w2.fst, a10 => () => run<int>(b11 => () => run<int>(k9, (a10 + b11)), 10)), w2.snd)))), less(a12, b13)), 50)))); 
            Thunk fmain = () => run<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>(x0 => () => run<Pair<Kont<Kont<int>>, Kont<int>>>(x0, pair<Kont<Kont<int>>, Kont<int>>(k1 => () => run<int>(k1, 8), x => { throw new Res<int>(x); })), unrec<Pair<Kont<Kont<int>>, Kont<int>>>((w2, rec3) => () => run<Kont<int>>(w2.fst, a18 => () => run<int>(b19 => () => run<Sum<Unit, Unit>>(z7 => match<Unit, Unit>(z7, u5 => () => run<Kont<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>>(u4 => () => run<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>(u4, rec3), x14 => () => run<Pair<Kont<Kont<int>>, Kont<int>>>(x14, pair<Kont<Kont<int>>, Kont<int>>(k15 => () => run<Kont<int>>(w2.fst, a16 => () => run<int>(b17 => () => run<int>(k15, (a16 - b17)), 1)), a8 => () => run<Kont<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>>(u4 => () => run<Kont<Pair<Kont<Kont<int>>, Kont<int>>>>(u4, rec3), x10 => () => run<Pair<Kont<Kont<int>>, Kont<int>>>(x10, pair<Kont<Kont<int>>, Kont<int>>(k11 => () => run<Kont<int>>(w2.fst, a12 => () => run<int>(b13 => () => run<int>(k11, (a12 - b13)), 2)), b9 => () => run<int>(w2.snd, (a8 + b9)))))))), u6 => () => run<int>(w2.snd, 1)), less(a18, b19)), 3)))); 
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
