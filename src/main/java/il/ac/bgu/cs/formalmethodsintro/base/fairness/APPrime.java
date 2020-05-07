package il.ac.bgu.cs.formalmethodsintro.base.fairness;

import java.util.Objects;

public class APPrime <Action,Prop> {
    private Action a;
    private Prop p;

    public APPrime(Prop p){
        this.p=p;
        this.a=null;
    }
    public APPrime(Action a, Prop p){
        this.a=a;
        this.p=p;
    }


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        APPrime<?, ?> apPrime = (APPrime<?, ?>) o;
        return Objects.equals(a, apPrime.a) &&
                Objects.equals(p, apPrime.p);
    }

    public String toString(){
        return "Action = "+ this.a+ " Prop = "+ this.p;
    }
    @Override
    public int hashCode() {
        return Objects.hash(a, p);
    }
}
