package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.fairness.APPrime;
import il.ac.bgu.cs.formalmethodsintro.base.fairness.FairnessCondition;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.*;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VeficationSucceeded;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationFailed;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationSucceeded;


/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 * More about facade: {@linkplain http://www.vincehuston.org/dp/facade.html}.
 */
public class FvmFacade {

    private static FvmFacade INSTANCE = null;


    /**
     * @return an instance of this class.
     */
    public static il.ac.bgu.cs.formalmethodsintro.base.FvmFacade get() {
        if (INSTANCE == null) {
            INSTANCE = new il.ac.bgu.cs.formalmethodsintro.base.FvmFacade();
        }
        return INSTANCE;
    }

    /**
     * Checks whether a transition system is action deterministic. I.e., if for
     * any given p and α there exists only a single tuple (p,α,q) in →. Note
     * that this must be true even for non-reachable states.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1)
            return false;
        Set<TSTransition<S, A>> first = ts.getTransitions();
        Set<TSTransition<S, A>> second = ts.getTransitions();
        for (TSTransition<S, A> trans : first) {
            for (TSTransition<S, A> trans2 : second
            ) {
                if (trans.getAction().equals(trans2.getAction()) && trans.getFrom().equals(trans2.getFrom())
                        && !(trans.getTo().equals(trans2.getTo())))
                    return false;

            }
        }
        return true;
    }

    /**
     * Checks whether an action is ap-deterministic (as defined in class), in
     * the context of a given {@link TransitionSystem}.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is ap-deterministic.
     */
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        //for state //init list of ap // add ap to list + check //
        HashMap<S, ArrayList<Set<P>>> labels = new HashMap<S, ArrayList<Set<P>>>();
        Map<S, Set<P>> funcLable = ts.getLabelingFunction();
        for (TSTransition tr : ts.getTransitions()) {
            if (labels.containsKey(tr.getFrom())) //in lables
                if (labels.get(tr.getFrom()).contains(funcLable.get(tr.getTo())))
                    return false;
                else
                    labels.get(tr.getFrom()).add(funcLable.get(tr.getTo()));
            else { // not in lables
                ArrayList<Set<P>> arr = new ArrayList<>();
                arr.add(funcLable.get(tr.getTo()));
                labels.put((S) tr.getFrom(), arr);
            }
        }//end for
        if (ts.getInitialStates().size() > 1)
            return false;

        return true;
    }

    /**
     * Checks whether an alternating sequence is an execution of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution of {@code ts}.
     * @return {@code true} iff {@code e} is an execution of {@code ts}.
     */
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isMaximalExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is an execution fragment of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution fragment of
     *            {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (e.isEmpty())
            return true;
        if (!ts.getStates().contains(e.head()))
            throw new StateNotFoundException(e.head());
        AlternatingSequence<A, S> seqTail = e.tail();
        S currState = e.head();
        while (!seqTail.isEmpty()) {
            A seqAct = seqTail.head();
            S nextState = seqTail.tail().head();
            if (!ts.getStates().contains(nextState))
                throw new StateNotFoundException(nextState);
            if (!ts.getActions().contains(seqAct))
                throw new ActionNotFoundException(seqAct);
            if (!ts.getTransitions().contains(new TSTransition<>(currState, seqAct, nextState)))
                return false;
            currState = nextState;
            seqTail = seqTail.tail().tail();
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an initial execution fragment
     * of a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an initial execution
     *            fragment of {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is a maximal execution fragment of
     * a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be a maximal execution fragment
     *            of {@code ts}.
     * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
     */
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isStateTerminal(ts, e.last()) && isExecutionFragment(ts, e);
    }

    /**
     * Checks whether a state in {@code ts} is terminal.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   The state being tested for terminality.
     * @return {@code true} iff state {@code s} is terminal in {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        return il.ac.bgu.cs.formalmethodsintro.base.FvmFacade.get().post(ts, s).isEmpty();
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> output = new HashSet<>();
        for (TSTransition<S, ?> trans : ts.getTransitions()) {
            if (trans.getFrom().equals(s))
                output.add(trans.getTo());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Post(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> output = new HashSet<>();
        for (S s : c) {
            output.addAll(il.ac.bgu.cs.formalmethodsintro.base.FvmFacade.get().post(ts, s));
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from
     * {@code s}, when action {@code a} is selected.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> output = new HashSet<>();
        for (TSTransition<S, ?> trans : ts.getTransitions()) {
            if (trans.getFrom().equals(s) && trans.getAction().equals(a))
                output.add(trans.getTo());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from any state
     * in {@code c}, when action {@code a} is selected.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> output = new HashSet<>();
        for (S s : c) {
            output.addAll(il.ac.bgu.cs.formalmethodsintro.base.FvmFacade.get().post(ts, s, a));
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> output = new HashSet<>();
        for (TSTransition<S, ?> trans : ts.getTransitions()) {
            if (trans.getTo().equals(s))
                output.add(trans.getFrom());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Pre(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> output = new HashSet<>();
        for (S s : c) {
            output.addAll(il.ac.bgu.cs.formalmethodsintro.base.FvmFacade.get().pre(ts, s));
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * {@code s}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> output = new HashSet<>();
        for (TSTransition<S, ?> trans : ts.getTransitions()) {
            if (trans.getTo().equals(s) && trans.getAction().equals(a))
                output.add(trans.getFrom());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * any state in {@code c}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> output = new HashSet<>();
        for (S s : c) {
            output.addAll(il.ac.bgu.cs.formalmethodsintro.base.FvmFacade.get().pre(ts, s, a));
        }
        return output;
    }

    /**
     * Implements the {@code reach(TS)} function.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @return All states reachable in {@code ts}.
     */
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reachStates = new HashSet<S>();
        Set<S> initStates = ts.getInitialStates();

        List<TSTransition<S, A>> initTran = new ArrayList<TSTransition<S, A>>();
        reachStates.addAll(initStates);
        for (TSTransition tr : ts.getTransitions())
            if (initStates.contains(tr.getFrom()))
                initTran.add(tr);

        Queue<TSTransition<S, A>> postS = new LinkedList<TSTransition<S, A>>();
        for (TSTransition<S, A> t : initTran)
            postS.add(t);

        TSTransition<S, A> tr = null;
        while (!postS.isEmpty()) {
            tr = postS.poll();
            if (!tr.getTo().equals(tr.getFrom())) {
                reachStates.add(tr.getTo());
                for (TSTransition<S, A> trPost : ts.getTransitions())
                    if (trPost.getFrom().equals(tr.getTo()) && !reachStates.contains(trPost.getTo()) && reachStates.contains(trPost.getFrom())) {
                        postS.add(trPost);
                    }
            }
        }

        return reachStates;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A>  Type of actions (in both systems).
     * @param <P>  Type of atomic propositions (in both systems).
     * @param ts1  The first transition system.
     * @param ts2  The second transition system.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, new HashSet<>());
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1>               Type of states in the first system.
     * @param <S2>               Type of states in the first system.
     * @param <A>                Type of actions (in both systems).
     * @param <P>                Type of atomic propositions (in both systems).
     * @param ts1                The first transition system.
     * @param ts2                The second transition system.
     * @param handShakingActions Set of actions both systems perform together.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> output = new TransitionSystem<>();
        Set<P> ap1 = ts1.getAtomicPropositions();
        Set<P> ap2 = ts2.getAtomicPropositions();
        output.addAllAtomicPropositions(ap1); // Ap1 UNION Ap2
        output.addAllAtomicPropositions(ap2);

        Set<S1> states1 = ts1.getStates();
        Set<S2> states2 = ts2.getStates();
        for (S1 st1 : states1 // adding all states
        ) {
            for (S2 st2 : states2
            ) {
                Pair<S1, S2> newP = new Pair<>(st1, st2);
                output.addState(newP);
                Set<P> newLabels = new HashSet<>();
                newLabels.addAll(ts1.getLabel(st1));
                newLabels.addAll(ts2.getLabel(st2));
                for (P label : newLabels)
                    output.addToLabel(newP, label);
            }
        }

        Set<S1> init1 = ts1.getInitialStates();
        Set<S2> init2 = ts2.getInitialStates();
        for (S1 st1 : init1 // adding all initial states
        ) {
            for (S2 st2 : init2
            ) {
                output.addInitialState(new Pair<>(st1, st2));
            }
        }

        Set<A> actions1 = ts1.getActions();
        Set<A> actions2 = ts2.getActions();
        output.addAllActions(actions1);// Act1 UNION Act2
        output.addAllActions(actions2);

        Set<TSTransition<S1, A>> trans1 = ts1.getTransitions();
        Set<TSTransition<S2, A>> trans2 = ts2.getTransitions();
        Pair<S1, S2> from;
        Pair<S1, S2> to;

        // ts1 transitions w/o handshake
        for (TSTransition<S1, A> tmptrans1 : trans1) {
            for (S2 sta2 : ts2.getStates()) {
                if (!handShakingActions.contains(tmptrans1.getAction())) {
                    from = new Pair<>(tmptrans1.getFrom(), sta2);
                    to = new Pair<>(tmptrans1.getTo(), sta2);
                    output.addTransitionFrom(from).action(tmptrans1.getAction()).to(to);
                }
            }

        }

        // ts2 transitions w/o handshake
        for (TSTransition<S2, A> tmptrans2 : trans2) {
            for (S1 sta1 : ts1.getStates()) {
                if (!handShakingActions.contains(tmptrans2.getAction())) {
                    from = new Pair<>(sta1, tmptrans2.getFrom());
                    to = new Pair<>(sta1, tmptrans2.getTo());
                    output.addTransitionFrom(from).action(tmptrans2.getAction()).to(to);
                }
            }
        }

        //transitions with handshake
        for (TSTransition<S1, A> tmptrans1 : trans1) {
            for (TSTransition<S2, A> tmptrans2 : trans2) {
                if (tmptrans1.getAction().equals(tmptrans2.getAction()) && handShakingActions.contains(tmptrans1.getAction())) {
                    from = new Pair<>(tmptrans1.getFrom(), tmptrans2.getFrom());
                    to = new Pair<>(tmptrans1.getTo(), tmptrans2.getTo());
                    output.addTransitionFrom(from).action(tmptrans2.getAction()).to(to);
                }
            }
        }

        return output;
    }

    /**
     * Creates a new {@link ProgramGraph} object.
     *
     * @param <L> Type of locations in the graph.
     * @param <A> Type of actions of the graph.
     * @return A new program graph instance.
     */
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraph<>();
    }

    /**
     * Interleaves two program graphs.
     *
     * @param <L1> Type of locations in the first graph.
     * @param <L2> Type of locations in the second graph.
     * @param <A>  Type of actions in BOTH GRAPHS.
     * @param pg1  The first program graph.
     * @param pg2  The second program graph.
     * @return Interleaved program graph.
     */
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> result = new ProgramGraph<Pair<L1, L2>, A>();
        // states
        for (L1 s1 : pg1.getLocations())
            for (L2 s2 : pg2.getLocations()) {
                result.addLocation(new Pair<L1, L2>(s1, s2));
            }
        //init state
        for (L1 initS1 : pg1.getInitialLocations())
            for (L2 initS2 : pg2.getInitialLocations())
                result.setInitial(new Pair<L1, L2>(initS1, initS2), true);

        //initialization actions

        for (List<String> lst1 : pg1.getInitalizations()) {
            for (List<String> lst2 : pg2.getInitalizations()) {
                List<String> lstResult = new ArrayList<String>();
                lstResult.addAll(lst1);
                lstResult.addAll(lst2);
                result.addInitalization(lstResult);
            }
        }


        // transition
        for (Pair<L1, L2> state : result.getLocations()) {

            for (PGTransition<L1, A> trans1 : pg1.getTransitions()) {
                if (trans1.getFrom().equals(state.first)) {
                    A act = trans1.getAction();
                    Pair<L1, L2> locTo = new Pair<L1, L2>(trans1.getTo(), state.second);
                    PGTransition tr = new PGTransition(state, trans1.getCondition(), trans1.getAction(), locTo);
                    result.addTransition(tr);
                }
            }

            for (PGTransition<L2, A> trans2 : pg2.getTransitions()) {
                if (trans2.getFrom().equals(state.second)) {
                    A act = trans2.getAction();
                    Pair<L1, L2> locTo = new Pair<L1, L2>(state.first, trans2.getTo());
                    PGTransition tr = new PGTransition(state, trans2.getCondition(), trans2.getAction(), locTo);
                    result.addTransition(tr);
                }
            }

        }// end for on locations

        return result;
    }

    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(
            Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTs = new TransitionSystem<>();
        ArrayList<String> regList = new ArrayList<>(c.getRegisterNames());
        ArrayList<String> inputList = new ArrayList<>(c.getInputPortNames());
        ArrayList<String> outputList = new ArrayList<>(c.getOutputPortNames());
        for (String reg : regList)
            newTs.addAtomicProposition(reg);
        for (String x : inputList)
            newTs.addAtomicProposition(x);
        for (String y : outputList)
            newTs.addAtomicProposition(y);
        int regInputMax = (int) Math.pow(2, regList.size());
        int inputNameMax = (int) Math.pow(2, inputList.size());
        Map<String, Boolean> initRegs = new HashMap<>();

        for (String reg : regList
        ) {
            initRegs.put(reg, false);
        }
        Set<Map<String, Boolean>> xAllPermu = new HashSet<>();
        for (int i = 0; i < inputNameMax; i++) {
            Map<String, Boolean> permu = new HashMap<>();
            String binary = Integer.toBinaryString(i);
            for (int j = 0; j < inputList.size(); j++) {
                boolean toPut = false;
                if (j < binary.length())
                    toPut = binary.charAt(binary.length() - j - 1) == '1';
                permu.put(inputList.get(j), toPut);
            }
            xAllPermu.add(permu);
            newTs.addInitialState(new Pair<>(permu, initRegs));// adding all permutations of the input with regs false
        }
        newTs.addAllActions(xAllPermu);// All actions are the permutations of the input
        for (int i = 1; i < regInputMax; i++) {
            Map<String, Boolean> regPermu = new HashMap<>();
            String binary = Integer.toBinaryString(i);
            for (int j = 0; j < regList.size(); j++) {
                boolean toPut = false;
                if (j < binary.length())// defining each bit of the reg tuple by the binary representation of the number
                    toPut = binary.charAt(binary.length() - j - 1) == '1';
                regPermu.put(regList.get(j), toPut);

            }
            for (Map<String, Boolean> xPermu : xAllPermu) {
                newTs.addState(new Pair<>(xPermu, regPermu));
            }
        }
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> from : newTs.getStates()) {// adding transitions and labels
            for (Map<String, Boolean> act : newTs.getActions()) {
                Map<String, Boolean> newReg = c.updateRegisters(from.getFirst(), from.getSecond());

                Pair<Map<String, Boolean>, Map<String, Boolean>> to = new Pair<>(act, newReg);
                newTs.addTransitionFrom(from).action(act).to(to);
            }

            // adding atomic propositions, checking for each states which of the inputs,regs or outputs are true
            for (Map.Entry<String, Boolean> x : from.getFirst().entrySet()) {
                if (x.getValue())
                    newTs.addToLabel(from, x.getKey());
            }
            for (Map.Entry<String, Boolean> reg : from.getSecond().entrySet()) {
                if (reg.getValue())
                    newTs.addToLabel(from, reg.getKey());
            }
            for (Map.Entry<String, Boolean> y : c.computeOutputs(from.getFirst(), from.getSecond()).entrySet()) {
                if (y.getValue())
                    newTs.addToLabel(from, y.getKey());
            }

        }
        return newTs;
    }

    /**
     * Creates a {@link TransitionSystem} from a program graph.
     *
     * @param <L>           Type of program graph locations.
     * @param <A>           Type of program graph actions.
     * @param pg            The program graph to be translated into a transition system.
     * @param actionDefs    Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program
     *                      graph.
     * @return A transition system representing {@code pg}.
     */
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {

        TransitionSystem<Pair<L, Map<String, Object>>, A, String> result = new TransitionSystem<Pair<L, Map<String, Object>>, A, String>();
        Queue<Pair<L, Map<String, Object>>> postS = new LinkedList<Pair<L, Map<String, Object>>>();

        //init states

        Set<Map<String, Object>> vals = new HashSet<>();

        for (List<String> lstCond : pg.getInitalizations())  // foreach cond -> cacl all the Var
            vals.add(valEfecet(lstCond, actionDefs));
        if (vals.isEmpty())
            vals.add(new HashMap<String, Object>());

        for (L location : pg.getInitialLocations()) {           // foreach init loc
            for (Map<String, Object> val : vals) {      //foreach calc val -> create in TS :state,AP and label

                Pair<L, Map<String, Object>> state = new Pair<>(location, val);
                postS.add(state);
                result.addState(state);         //add state
                result.addInitialState(state);
                if (location instanceof List) {
                    for (int i = 0; i < ((List) location).size(); i++) {
                        result.addAtomicProposition(((List) location).get(i).toString());
                        if (state.first instanceof List) {
                            for (int j = 0; j < ((List) state.first).size(); j++)
                                result.addToLabel(state, ((List) state.first).get(j).toString());
                        } else
                            result.addToLabel(state, state.first.toString());       //tag loc
                    }
                    // result.addToLabel(state,state.first.toString());       //tag loc
                } else {
                    result.addAtomicProposition(location.toString());      //add AP loc
                    result.addToLabel(state, state.first.toString());       //tag loc

                }


                for (String strVal : val.keySet()) {
                    result.addAtomicProposition(strVal + " = " + val.get(strVal));      //add AP cond(var)
                    result.addToLabel(state, strVal + " = " + val.get(strVal));         //add label cond(var)
                }

            } //end for on vals
        }// end for on init location

        while (!postS.isEmpty()) {
            Pair<L, Map<String, Object>> state = postS.poll();
            for (PGTransition<L, A> tr : pg.getTransitions()) { // find TR that start from state location
                if (tr.getFrom().equals(state.first))
                    if (ConditionDef.evaluate(conditionDefs, state.second, tr.getCondition())) { // can pass to new state

                        Map<String, Object> newVal = ActionDef.effect(actionDefs, state.second, tr.getAction());
                        if (newVal != null) {
                            Pair<L, Map<String, Object>> postState = new Pair<L, Map<String, Object>>(tr.getTo(), newVal);
                            if (!result.getStates().contains(postState)) {
                                postS.add(postState);
                                result.addState(postState);
                            }
                            result.addAction(tr.getAction());
                            result.addTransitionFrom(state).action(tr.getAction()).to(postState);
                            if (postState.first instanceof List) {
                                for (int i = 0; i < ((List) postState.first).size(); i++) {
                                    result.addAtomicProposition(((List) postState.first).get(i).toString());//AP newLoc
                                    result.addToLabel(postState, ((List) postState.first).get(i).toString());//tag newLoc
                                }
                            } else {
                                result.addAtomicProposition(postState.first.toString()); //AP newLoc
                                result.addToLabel(postState, postState.first.toString()); //tag newLoc

                            }

                            for (String strVal : newVal.keySet()) {
                                result.addAtomicProposition(strVal + " = " + newVal.get(strVal));      //add AP cond(var)
                                result.addToLabel(postState, strVal + " = " + newVal.get(strVal));         //add label cond(var)
                            }
                        }
                    }
            }
        }// end while

        return result;

    }

    private Map<String, Object> valEfecet(List<String> lstCond, Set<ActionDef> actionDefs) {
        Map<String, Object> val = new HashMap<>();
        for (String cond : lstCond) // calc val
            val = ActionDef.effect(actionDefs, val, cond);

        return val;
    }


    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs  The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {

        Set<ActionDef> actions = Collections.singleton(new ParserBasedActDef());
        Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());
        return transitionSystemFromChannelSystem(cs, actions, conditions);
    }

    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {

        List<ProgramGraph<L, A>> csPGs = cs.getProgramGraphs();
        ProgramGraph<List<L>, A> bigPG = new ProgramGraph<>();
        ProgramGraph<L, A> initPG = csPGs.get(0);

        //locations and initials
        for (L loc : initPG.getLocations()) {
            List<L> newLoc = new LinkedList<>();
            newLoc.add(loc);
            bigPG.addLocation(newLoc);
            if (initPG.getInitialLocations().contains(loc))
                bigPG.setInitial(newLoc, true);
        }

        //initializations
        for (List<String> initialize :
                initPG.getInitalizations()) {
            bigPG.addInitalization(initialize);
        }

        //transitions
        for (PGTransition<L, A> trans : initPG.getTransitions()) {
            List<L> from = Arrays.asList(trans.getFrom());
            List<L> to = Arrays.asList(trans.getTo());
            bigPG.addTransition(new PGTransition<>(from, trans.getCondition(), trans.getAction(), to));
        }
        bigPG.setName(initPG.getName());

        // start from 1 because we dealed with 0
        for (int i = 1; i < csPGs.size(); i++) {
            bigPG = addGraph(bigPG, csPGs.get(i));
        }
        Set<ActionDef> act = new LinkedHashSet<>();
        act.add(new ParserBasedInterleavingActDef());
        act.add(new ParserBasedActDef());
        Set<ConditionDef> cons = new HashSet<>();
        cons.add(new ParserBasedCondDef());
        return transitionSystemFromProgramGraph(bigPG, act, cons);
    }

    private <L, A> ProgramGraph<List<L>, A> addGraph(ProgramGraph<List<L>, A> bigPG, ProgramGraph<L, A> currPG) {

        ProgramGraph<List<L>, A> newBigPG = new ProgramGraph<>();
        ParserBasedInterleavingActDef inParser = new ParserBasedInterleavingActDef();

        //locations and initials
        for (List<L> bigLoc : bigPG.getLocations()) {
            for (L smallLoc : currPG.getLocations()) {
                List<L> newLoc = new LinkedList<>(bigLoc);
                newLoc.add(smallLoc);
                newBigPG.addLocation(newLoc);
                if (bigPG.getInitialLocations().contains(bigLoc) && currPG.getInitialLocations().contains(smallLoc))
                    newBigPG.setInitial(newLoc, true);
            }
        }

        //initializations
        if (!bigPG.getInitalizations().isEmpty()) {
            for (List<String> initialBig :
                    bigPG.getInitalizations()) {
                if (currPG.getInitalizations().isEmpty()) {
                    List<String> newInitial = new ArrayList<>(initialBig);
                    newBigPG.addInitalization(newInitial);
                } else
                    for (List<String> initialSmall :
                            currPG.getInitalizations()) {
                        List<String> newInitial = new ArrayList<>(initialBig);
                        newInitial.addAll(initialSmall);
                        newBigPG.addInitalization(newInitial);
                    }
            }
        } else {
            for (List<String> initialSmall :
                    currPG.getInitalizations()) {
                newBigPG.addInitalization(initialSmall);
            }
        }
        //transitions
        //two sided big graph
        for (PGTransition<List<L>, A> bigTrans : bigPG.getTransitions()) {
            String bigAct = bigTrans.getAction().toString();
            if (!inParser.isOneSidedAction(bigAct)) {
                for (L loc : currPG.getLocations()) {
                    List<L> from = new LinkedList<>(bigTrans.getFrom());
                    List<L> to = new LinkedList<>(bigTrans.getTo());
                    from.add(loc);
                    to.add(loc);
                    newBigPG.addTransition(new PGTransition<>(from, bigTrans.getCondition(), bigTrans.getAction(), to));
                }
            }
            //one sided action
            else {
                for (PGTransition<L, A> smallTrans : currPG.getTransitions()) {
                    boolean isOneSided = false;
                    String smallAct = smallTrans.getAction().toString();
                    if (bigAct.contains("?")) {
                        if (smallAct.contains("!") && smallAct.substring(0, smallAct.indexOf('!'))
                                .equals(bigAct.substring(0, bigAct.indexOf('?'))))
                            isOneSided = true;


                    } else {
                        if (bigAct.contains("!")) {
                            if (smallAct.contains("?") && smallAct.substring(0, smallAct.indexOf('?'))
                                    .equals(bigAct.substring(0, bigAct.indexOf('!'))))
                                isOneSided = true;
                        } else {
                            continue;
                        }
                    }
                    if (isOneSided) {

                        List<L> from = new LinkedList<>(bigTrans.getFrom());
                        List<L> to = new LinkedList<>(bigTrans.getTo());
                        from.add(smallTrans.getFrom());
                        to.add(smallTrans.getTo());
                        String mergeAct = bigAct + "|" + smallAct;
                        System.out.println(mergeAct);
                        String mergeCond = CondAnd(bigTrans.getCondition(), smallTrans.getCondition());
                        newBigPG.addTransition(new PGTransition<>(from, mergeCond, (A) mergeAct, to));

                    }
                }
            }
        }
        //two sided small graph
        for (PGTransition<L, A> smallTrans : currPG.getTransitions()) {
            String smallAct = smallTrans.getAction().toString();
            if (!inParser.isOneSidedAction(smallAct)) {
                for (List<L> locList : bigPG.getLocations()) {
                    List<L> from = new LinkedList<>(locList);
                    List<L> to = new LinkedList<>(locList);
                    from.add(smallTrans.getFrom());
                    to.add(smallTrans.getTo());
                    newBigPG.addTransition(new PGTransition<>(from, smallTrans.getCondition(), smallTrans.getAction(), to));
                }
            }
        }
        return newBigPG;

    }

    private String CondAnd(String cond1, String cond2) {
        if (cond1.length() == 0 || cond2.length() == 0)
            return cond1 + cond2;
        else
            return cond1 + " && " + cond2;
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        NanoPromelaParser.StmtContext stmtContext = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        return pgFromNp(stmtContext);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        NanoPromelaParser.StmtContext stmtContext = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        return pgFromNp(stmtContext);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        NanoPromelaParser.StmtContext stmtContext = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        return pgFromNp(stmtContext);
    }

    private ProgramGraph<String, String> pgFromNp(NanoPromelaParser.StmtContext stmtContext) {
        ProgramGraph<String, String> pg = new ProgramGraph<String, String>();
        Map<String, Set<PGTransition<String, String>>> subsAndTrans = new HashMap<String, Set<PGTransition<String, String>>>();
        createSub(stmtContext, subsAndTrans); // create (subText , all trans for this sub)  recursive function
        loadLocation(pg, subsAndTrans, stmtContext);  //load pg from subsAndTrans
        return pg;
    }

    private void loadLocation(ProgramGraph<String, String> pg, Map<String, Set<PGTransition<String, String>>> subsAndTrans, NanoPromelaParser.StmtContext stmtContext) {
        pg.addLocation(stmtContext.getText()); // start location
        pg.setInitial(stmtContext.getText(), true);
        Queue<String> locations = new LinkedList<String>();
        locations.add(stmtContext.getText());
        while (!locations.isEmpty())
            if (!locations.peek().equals("") && subsAndTrans.get(locations.peek()) != null) {
                for (PGTransition<String, String> tr : subsAndTrans.get(locations.poll())) {
                    if (!pg.getLocations().contains(tr.getTo())) {
                        locations.add(tr.getTo());
                        pg.addLocation(tr.getTo());
                    }
                    pg.addTransition(tr);
                }//end for
            } else
                pg.addLocation(locations.poll());


    }

    private void createSub(NanoPromelaParser.StmtContext sc, Map<String, Set<PGTransition<String, String>>> subsAndTrans) {
        //if we contain all the subs
        if (subsAndTrans.containsKey(sc.getText()))
            return;

        // not need to call again to sub.. atomic or asstmt or chan or skip
        if (sc.atomicstmt() != null || sc.assstmt() != null || sc.chanreadstmt() != null || sc.chanwritestmt() != null || sc.skipstmt() != null) {
            Set<PGTransition<String, String>> trSet = new HashSet<PGTransition<String, String>>();
            PGTransition<String, String> tr = new PGTransition<String, String>(sc.getText(), "", sc.getText(), ""); //location to = exit
            trSet.add(tr);
            subsAndTrans.put(sc.getText(), trSet);
        } else if (sc.ifstmt() != null) {
            Set<PGTransition<String, String>> trSet = new HashSet<PGTransition<String, String>>();
            PGTransition<String, String> newTr;
            for (NanoPromelaParser.OptionContext op : sc.ifstmt().option()) {
                createSub(op.stmt(), subsAndTrans);  //  opt-text are now in the Map object with the trans
                for (PGTransition<String, String> tr : subsAndTrans.get(op.stmt().getText())) {  // create trans from the IF...FI to the OPT
                    if (tr.getCondition().equals("") && op.boolexpr().getText().equals(""))     // no cond
                        newTr = new PGTransition(sc.getText(), "", tr.getAction(), tr.getTo().toString());
                    else if (tr.getCondition().equals(""))                                      // only opt cond
                        newTr = new PGTransition(sc.getText(), "(" + op.boolexpr().getText() + ")", tr.getAction(), tr.getTo().toString());
                    else if (op.boolexpr().getText().equals(""))                                 // only tran cond
                        newTr = new PGTransition(sc.getText(), "(" + tr.getCondition() + ")", tr.getAction(), tr.getTo().toString());
                    else                                                                        // tran cond & opt cond
                        newTr = new PGTransition(sc.getText(), "(" + op.boolexpr().getText() + ") && (" + tr.getCondition() + ")", tr.getAction(), tr.getTo().toString());
                    trSet.add(newTr);
                }// end for - the create for IF..FI to OPT
            }// end for - do for all OPT
            subsAndTrans.put(sc.getText(), trSet);
        } else if (sc.dostmt() != null) { // do stmt , need to call again to createSub foreach option

            for (NanoPromelaParser.OptionContext op : sc.dostmt().option()) {
                createSub(op.stmt(), subsAndTrans);   //  opt text are now in the Map object with the trans

                HashSet<String> locations = new HashSet<String>();
                String stmtNext = sc.getText();
                String opStmt = op.stmt().getText();
                loopLoopAndStmtLoop(subsAndTrans, sc.getText(), opStmt, stmtNext, op.boolexpr().getText(), locations);   //loop rules: stmt;loop-->loop & loop-->loop
            }
            String notOnCond = "";    //!(all conds)  for the exit stmt
            for (int i = 0; i < sc.dostmt().option().size(); i++) {
                if (i == sc.dostmt().option().size() - 1)
                    notOnCond = notOnCond + "!(" + sc.dostmt().option(i).boolexpr().getText() + ")";
                else
                    notOnCond = notOnCond + "!(" + sc.dostmt().option(i).boolexpr().getText() + ") && ";
            }

            PGTransition<String, String> newTr = new PGTransition<String, String>(sc.getText(), notOnCond, "", ""); //to = exit
            if (!subsAndTrans.containsKey(sc.getText()))
                subsAndTrans.put(sc.getText(), new HashSet<PGTransition<String, String>>());
            subsAndTrans.get(sc.getText()).add(newTr);

        } else {// case ";"
            createSub(sc.stmt(0), subsAndTrans);
            createSub(sc.stmt(1), subsAndTrans);
            stmtStmtCase(subsAndTrans, sc.getText(), sc.stmt(0).getText(), sc.stmt(1).getText(), new HashSet<String>());
        }
    }

    private void stmtStmtCase(Map<String, Set<PGTransition<String, String>>> subsAndTrans, String mainStmt, String firstStmt, String secondStmt, HashSet<String> locations) {
        if (!locations.add(firstStmt))
            return;
        if (subsAndTrans.containsKey(firstStmt))
            for (PGTransition<String, String> tr : subsAndTrans.get(firstStmt)) {

                if (!subsAndTrans.containsKey(mainStmt))
                    subsAndTrans.put(mainStmt, new HashSet<PGTransition<String, String>>());

                if (tr.getTo().equals(""))      //case stmt1;stmt2 ->stmt2
                    subsAndTrans.get(mainStmt).add(new PGTransition<String, String>(mainStmt, tr.getCondition(), tr.getAction(), secondStmt));
                else {                           //case stmt1;stmt1.1;stmt2 ->stmt1.1;stmt2
                    subsAndTrans.get(mainStmt).add(new PGTransition<String, String>(mainStmt, tr.getCondition(), tr.getAction(), tr.getTo() + ";" + secondStmt));
                    stmtStmtCase(subsAndTrans, tr.getTo() + ";" + secondStmt, tr.getTo(), secondStmt, locations);
                }
            }
    }

    private void loopLoopAndStmtLoop(Map<String, Set<PGTransition<String, String>>> subsAndTrans, String curStmt, String opStmt, String stmstNext, String cond, HashSet<String> locations) {
        if (!locations.add(opStmt))
            return;
        for (PGTransition<String, String> tr : subsAndTrans.get(opStmt)) {
            String toStmt;
            if (tr.getTo().equals("")) //loop-->loop
                toStmt = stmstNext;
            else                       //stmt;loop
                toStmt = tr.getTo() + ";" + stmstNext;

            String newCond = createCond(tr, cond);

            PGTransition<String, String> newTr = new PGTransition<String, String>(curStmt, newCond, tr.getAction(), toStmt);
            if (!subsAndTrans.containsKey(curStmt))
                subsAndTrans.put(curStmt, new HashSet<PGTransition<String, String>>());
            subsAndTrans.get(curStmt).add(newTr);

            if (!tr.getTo().equals("")) {                                             //loop->loop case
                loopLoopAndStmtLoop(subsAndTrans, toStmt, tr.getTo(), stmstNext, "", locations); //cond is true
            }
        }

    }

    private String createCond(PGTransition<String, String> tr, String cond) {
        String newCond;
        if (tr.getCondition().equals("") && cond.equals(""))
            newCond = "";
        else if (tr.getCondition().equals(""))
            newCond = "(" + cond + ")";
        else if (cond.equals(""))
            newCond = "(" + tr.getCondition() + ")";
        else
            newCond = "(" + tr.getCondition() + ") && (" + cond + ")";
        return newCond;

    }

    /**
     * Creates a transition system from a transition system and an automaton.
     *
     * @param <Sts>  Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    The automaton.
     * @return The product of {@code ts} with {@code aut}.
     */
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
                                                                                Automaton<Saut, P> aut) {
        TransitionSystem<Pair<Sts, Saut>, A, Saut> output = new TransitionSystem<>();
        output.addAllActions(ts.getActions());
        Set<Saut> autoStates = aut.getTransitions().keySet();
        Set<Sts> tsStates = ts.getStates();
        for (Saut aState : autoStates) {
            for (Sts tState : tsStates) {
                Pair<Sts, Saut> toAdd = new Pair<>(tState, aState);
                output.addState(toAdd);
            }
        }
        for (TSTransition<Sts, A> trans : ts.getTransitions()) {
            for (Saut from : autoStates)
                if (aut.getTransitions().get(from).get(ts.getLabel(trans.getTo())) != null)
                    for (Saut to : aut.getTransitions().get(from).get(ts.getLabel(trans.getTo()))) {
                        output.addTransition(new TSTransition<>(new Pair<>(trans.getFrom(), from), trans.getAction(), new Pair<>(trans.getTo(), to)));
                    }
        }
        //init states
        for (Saut aInState : aut.getInitialStates()) {
            for (Sts tInState : ts.getInitialStates()) {
                if (aut.getTransitions().get(aInState) != null && aut.getTransitions().get(aInState).get(ts.getLabel(tInState)) != null)
                    for (Saut nextState : aut.getTransitions().get(aInState).get(ts.getLabel(tInState))) {
                        output.addInitialState(new Pair<>(tInState, nextState));
                    }
            }
        }
        removeNotReach(output);
        addAtomicAndLabel(output);
        return output;
    }

    private <Sts, Saut, A> void addAtomicAndLabel(TransitionSystem<Pair<Sts, Saut>, A, Saut> output) {
        for (Pair<Sts, Saut> state : output.getStates()) {
            output.addAtomicProposition(state.second);
            output.addToLabel(state, state.second);
        }
    }

    private <Sts, Saut, A> void removeNotReach(TransitionSystem<Pair<Sts, Saut>, A, Saut> output) {
        Set<Pair<Sts, Saut>> reach = reach(output);
        Set<Pair<Sts, Saut>> toDeleteState = new HashSet<>();
        Set<TSTransition<Pair<Sts, Saut>, A>> toDeleteTrans = new HashSet<>();
        for (Pair<Sts, Saut> st : output.getStates()) {
            if (!reach.contains(st)) {
                toDeleteState.add(st);
                for (Saut lbl : output.getLabel(st))
                    output.removeLabel(st, lbl);
                for (TSTransition<Pair<Sts, Saut>, A> trans : output.getTransitions())
                    if (st.equals(trans.getFrom()) || st.equals(trans.getTo()))
                        toDeleteTrans.add(trans);
            }
        }
        for (TSTransition<Pair<Sts, Saut>, A> trans : toDeleteTrans)
            output.removeTransition(trans);
        for (Pair<Sts, Saut> st : toDeleteState)
            output.removeState(st);
    }

    /**
     * Verify that a system satisfies an omega regular property.
     *
     * @param <S>    Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    A Büchi automaton for the words that do not satisfy the
     *               property.
     * @return A VerificationSucceeded object or a VerificationFailed object
     * with a counterexample.
     */
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
                                                                              Automaton<Saut, P> aut) {
        TransitionSystem<Pair<S, Saut>, A, Saut> product = product(ts, aut);
        Set<Pair<S, Saut>> prodStates = product.getStates();
        Set<Pair<S, Saut>> prodInitalStates = product.getInitialStates();
        ArrayList<S> loop = new ArrayList<S>();
        ArrayList<S> pre = new ArrayList<S>();
        HashSet<Pair<S, Saut>> allStates = new HashSet<Pair<S, Saut>>();
        for (Pair<S, Saut> state : prodStates)
            for (Saut label : product.getLabel(state))
                if (aut.getAcceptingStates().contains(label) && reach(product).contains(state)) {
                    loop.clear();
                    allStates.clear();
                    VerificationFailed<S> verification = new VerificationFailed<S>();
                    if (isLoop(state, product, state, allStates, loop)) { //if we found loop
                        findPrefix(prodInitalStates, pre, allStates, state, product, verification);
                        Collections.reverse(loop);
                        loop.add(state.first);
                        verification.setCycle(loop);
                        return verification;
                    }
                }

        return new VerificationSucceeded<>();
    }

    private <S, Saut, A> void findPrefix(Set<Pair<S, Saut>> prodInitalStates, ArrayList<S> pre, HashSet<Pair<S, Saut>> allStates,
                                         Pair<S, Saut> state, TransitionSystem<Pair<S, Saut>, A, Saut> product, VerificationFailed<S> verification) {
        for (Pair<S, Saut> prodInitState : prodInitalStates) {
            pre.clear();
            allStates.clear();
            boolean isloop = isLoop(state, product, prodInitState, allStates, pre);
            if (isloop) {
                pre.add(prodInitState.first);
                Collections.reverse(pre);
                pre.add(state.first);
                verification.setPrefix(pre);
                break;
            }
        }
    }

    private <S, Saut, A> boolean isLoop(Pair<S, Saut> currState, TransitionSystem<Pair<S, Saut>, A, Saut> product, Pair<S, Saut> nextState, HashSet<Pair<S, Saut>> allStates, ArrayList<S> loop) {
        Set<Pair<S, Saut>> currStatePosts = post(product, nextState);
        S currS = currState.first;
        S postS;
        for (Pair<S, Saut> post : currStatePosts) {
            postS = post.first;
            if (currS.equals(postS)) // find loop
                return true;
            else if (allStates.add(post) && isLoop(currState, product, post, allStates, loop)) {
                loop.add(postS);
                return true;
            }
        }

        return false;
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param <L>    Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        return multiGNBA2NBA(mulAut);
    }

    private <St, L> Automaton<Pair<St, Integer>, L> multiGNBA2NBA(MultiColorAutomaton<St, L> mulAut) {
        Automaton<Pair<St, Integer>, L> output = new Automaton<>();
        if (mulAut.getColors().isEmpty())
            return output;
        List<Integer> colors = new ArrayList<>(mulAut.getColors());
        for (int i = 0; i < colors.size(); i++) {
            Integer nextColor;
            if (i == colors.size() - 1) {
                nextColor = colors.get(0);
            } else
                nextColor = colors.get(i + 1);
            Integer color = colors.get(i);
            for (Map.Entry<St, Map<Set<L>, Set<St>>> trans : mulAut.getTransitions().entrySet()) {
                Pair<St, Integer> from = new Pair<>(trans.getKey(), color);
                if (i == 0) {
                    if (mulAut.getAcceptingStates(color).contains(trans.getKey()))
                        output.setAccepting(from);
                    if (mulAut.getInitialStates().contains(trans.getKey()))
                        output.setInitial(from);
                }
                for (Map.Entry<Set<L>, Set<St>> transEntry : trans.getValue().entrySet()) {
                    for (St state : transEntry.getValue()) {
                        Pair<St, Integer> to;
                        if (mulAut.getAcceptingStates(colors.get(i)).contains(trans.getKey()))
                            to = new Pair<>(state, nextColor);
                        else
                            to = new Pair<>(state, color);
                        output.addTransition(from, transEntry.getKey(), to);
                    }
                }
            }
        }
        return output;
    }

    private <L> void acceptingUntilState(Set<Set<LTL<L>>> allTransS, ArrayList<LTL<L>> allUntils, MultiColorAutomaton<Set<LTL<L>>, L> gnba) {
        for (Set<LTL<L>> trnS : allTransS)
            for (LTL<L> unt : allUntils) {
                boolean right = trnS.contains(((Until<L>) unt).getRight());
                int color = allUntils.indexOf(unt);
                if (right || !trnS.contains(unt))
                    gnba.setAccepting(trnS, color);
            }
    }

    private <L> MultiColorAutomaton<Set<LTL<L>>, L> initGNBA(List<LTL<L>> expressions, Set<Set<LTL<L>>> clos, LTL<L> ltl) {
        MultiColorAutomaton<Set<LTL<L>>, L> gnba = new MultiColorAutomaton<>();
        HashSet<Until<L>> allUntil = new HashSet<>();
        HashSet<Next<L>> allNext = new HashSet<>();
        update_Next_Until(allNext, allUntil, expressions);
        createSourceAndDestination(gnba, clos, allUntil, allNext);
        Set<Set<LTL<L>>> allTrans = gnba.getTransitions().keySet();

        for (Set<LTL<L>> trnS : allTrans)
            if (trnS.contains(ltl))
                gnba.setInitial(trnS);


        return gnba;
    }

    private <L> void createSourceAndDestination(MultiColorAutomaton<Set<LTL<L>>, L> gnba, Set<Set<LTL<L>>> clos,
                                                HashSet<Until<L>> allUntil, HashSet<Next<L>> allNext) {
        HashSet<L> aps = new HashSet<L>();
        for (Set<LTL<L>> src : clos)
            for (Set<LTL<L>> des : clos) {
                if (containNextAndUntil(gnba, src, des, allNext, allUntil)) {
                    for (LTL<L> l : src) {
                        if (l instanceof AP)
                            aps.add(((AP<L>) l).getName());
                        gnba.addTransition(src, aps, des);
                    }
                }
            }
    }

    private <L> boolean containNextAndUntil(MultiColorAutomaton<Set<LTL<L>>, L> gnba, Set<LTL<L>> src, Set<LTL<L>> des, HashSet<Next<L>> allNext, HashSet<Until<L>> allUntil) {
        boolean next;
        boolean until;
        for (Until<L> unt : allUntil) {
            boolean right = src.contains(unt.getRight());
            boolean left = src.contains(unt.getLeft());
            boolean desContain = des.contains(unt);
            boolean srcContain = src.contains(unt);
            if ((desContain && left) || right) {
                if (!srcContain)
                    return false;
            } else if (srcContain) {
                return false;
            }
        }
        until = true;

        for (Next<L> nxt : allNext) {
            boolean desContain = des.contains(nxt.getInner());
            if (src.contains(nxt)) {
                if (!desContain)
                    return false;
            } else if (desContain)
                return false;
        }
        next = true;

        return next && until;
    }

    private <L> void update_Next_Until(HashSet<Next<L>> allNext, HashSet<Until<L>> allUntil, List<LTL<L>> expressions) {
        for (LTL<L> l : expressions)
            if (l instanceof Until)
                allUntil.add((Until<L>) l);
            else if (l instanceof Next)
                allNext.add((Next<L>) l);
    }


    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        List<LTL<L>> expressions = new ArrayList<>();
        ltlToExpressions(ltl, expressions);
        Set<Set<LTL<L>>> clos = new HashSet<>();

        // create closure
        HashSet st = new HashSet<>();
        if (expressions.contains(LTL.true_()))
            st.add(LTL.true_());
        clos.add(st);

        for (LTL<L> l : expressions) {
            Set<Set<LTL<L>>> allState = new HashSet<>(clos);
            if (l instanceof Next) {
                NextToClousre(l, allState, clos);
            } else if (l instanceof AP) {
                APToClousre(l, allState, clos);
            } else if (l instanceof And) {
                for (Set<LTL<L>> s : allState) {
                    boolean right = s.contains(((And<L>) l).getRight());
                    boolean left = s.contains(((And<L>) l).getLeft());
                    if (right && left)
                        s.add(l);
                    else
                        s.add(LTL.not(l));
                }
            } else if (l instanceof Until) {
                for (Set<LTL<L>> s : allState) {
                    boolean right = s.contains(((Until<L>) l).getRight());
                    boolean left = s.contains(((Until<L>) l).getLeft());
                    if (right)
                        s.add(l);
                    else if (left) {
                        Set<LTL<L>> notOnSub = new HashSet<LTL<L>>(s);
                        notOnSub.add(LTL.not(l));
                        clos.add(notOnSub);
                        s.add(l);
                    } else
                        s.add(LTL.not(l));
                }
            }
        }
        // end of create closure

        MultiColorAutomaton<Set<LTL<L>>, L> gnba = initGNBA(expressions, clos, ltl); // with init state

        //gnba accept state


        ArrayList<LTL<L>> allUntils = new ArrayList<>();
        boolean gotUntil = false;
        for (LTL<L> l : expressions) {
            if (l instanceof Until) {
                gotUntil = true;
                allUntils.add(l);
            }
        }

        Set<Set<LTL<L>>> allTransS = gnba.getTransitions().keySet();
        if (gotUntil) {
            acceptingUntilState(allTransS, allUntils, gnba);
        } else {
            for (Set<LTL<L>> trnS : allTransS)
                gnba.setAccepting(trnS, 0);
        }
        return GNBA2NBA(gnba);
    }

    private <L> void APToClousre(LTL<L> l, Set<Set<LTL<L>>> allState, Set<Set<LTL<L>>> clos) {
        for (Set<LTL<L>> s : allState) {
            Set<LTL<L>> notOnSub = new HashSet<LTL<L>>(s);
            notOnSub.add(LTL.not(l));
            clos.add(notOnSub);
            s.add(l);
        }
    }

    private <L> void NextToClousre(LTL<L> l, Set<Set<LTL<L>>> allState, Set<Set<LTL<L>>> clos) {
        for (Set<LTL<L>> s : allState) {
            Set<LTL<L>> notOnSub = new HashSet<LTL<L>>(s);
            notOnSub.add(LTL.not(l));
            clos.add(notOnSub);
            s.add(l);
        }
    }

    private <L> void ltlToExpressions(LTL<L> ltl, List<LTL<L>> expressions) {
        if (ltl instanceof TRUE) {
            addIfNotContain(expressions, ltl);
        } else if (ltl instanceof AP) {
            addIfNotContain(expressions, ltl);
        } else if (ltl instanceof Not) {
            LTL<L> inner = ((Not<L>) ltl).getInner();
            ltlToExpressions(inner, expressions);
        } else if (ltl instanceof Next) {
            ltl2Next(ltl, expressions);
        } else if (ltl instanceof And) {
            ltl2And(ltl, expressions);
        } else if (ltl instanceof Until) {
            ltl2Until(ltl, expressions);
        }
    }

    private <L> void ltl2Next(LTL<L> ltl, List<LTL<L>> expressions) {
        LTL<L> inner = ((Next<L>) ltl).getInner();
        ltlToExpressions(inner, expressions);
        addIfNotContain(expressions, ltl);
    }

    private <L> void ltl2Until(LTL<L> ltl, List<LTL<L>> expressions) {
        LTL<L> right = ((Until<L>) ltl).getRight();
        LTL<L> left = ((Until<L>) ltl).getLeft();
        ltlToExpressions(left, expressions);
        ltlToExpressions(right, expressions);
        addIfNotContain(expressions, ltl);
    }

    private <L> void ltl2And(LTL<L> ltl, List<LTL<L>> expressions) {
        LTL<L> right = ((And<L>) ltl).getRight();
        LTL<L> left = ((And<L>) ltl).getLeft();
        ltlToExpressions(left, expressions);
        ltlToExpressions(right, expressions);
        addIfNotContain(expressions, ltl);
    }

    private <L> void addIfNotContain(List lst, LTL<L> p) {
        if (!lst.contains(p))
            lst.add(p);
    }

    public <S, A, P> VerificationResult<S> verifyFairLTLFormula(TransitionSystem<S, A, P> ts, FairnessCondition<A> fc, LTL<P> ltl) {
        TransitionSystem<Pair<S, A>, A, APPrime<A, P>> tsPrime = new TransitionSystem<>();
        for (P p : ts.getAtomicPropositions()) {
            APPrime<A, P> newP = new APPrime<>(p);
            tsPrime.addAtomicProposition(newP);
        }
        tsPrime.addAllActions(ts.getActions());
        for (S s : ts.getStates())
            for (A a : ts.getActions()) {
                APPrime<A, P> triggered = new APPrime<>(a, (P) "t");
                APPrime<A, P> enabled = new APPrime<>(a, (P) "e");
                Pair<S, A> newSt = new Pair<>(s, a);
                tsPrime.addAtomicProposition(triggered);
                tsPrime.addAtomicProposition(enabled);
                tsPrime.addToLabel(newSt, triggered);
                for (P lbl : ts.getLabel(s)) {
                    tsPrime.addToLabel(newSt, new APPrime<>(lbl));
                }
                if (ts.getInitialStates().contains(s))
                    tsPrime.addInitialState(newSt);
                else
                    tsPrime.addState(newSt);
            }
        for (TSTransition<S, A> trans : ts.getTransitions()) {
            Set<Pair<S, A>> fromStates = new HashSet<>();
            Pair<S, A> to = null;
            for (Pair<S, A> state : tsPrime.getStates()) {
                if (trans.getFrom() == state.first)
                    fromStates.add(state);
                if (trans.getTo() == state.first && trans.getAction() == state.second)
                    to = state;
            }
            for (Pair<S, A> from : fromStates) {
                tsPrime.addTransitionFrom(from).action(trans.getAction()).to(to);
                tsPrime.addToLabel(from, new APPrime<>(trans.getAction(), (P) "e"));
            }
        }
        LTL<APPrime<A, P>> uncond = getUncond(fc.getUnconditional());
        LTL<APPrime<A, P>> strong = getStrong(fc.getStrong());
        LTL<APPrime<A, P>> weak = getWeak(fc.getWeak());
        And<APPrime<A, P>> first = new And<>(uncond, strong);
        And<APPrime<A, P>> phiF = new And<>(first, weak);// Phi F
        LTL<APPrime<A, P>> converted = convertLTL(ltl); /// Phi
        Not<APPrime<A, P>> notPhiF = new Not<>(phiF);// PhiF -> Phi = not PhiF or Phi
        Not<APPrime<A, P>> notIfOrThen = ltlOr(notPhiF, converted); // not PhiF or Phi
        Automaton<?, APPrime<A, P>> finalAuto = LTL2NBA(notIfOrThen);
        VerificationResult<Pair<S, A>> unformatResult = verifyAnOmegaRegularProperty(tsPrime, finalAuto);
        if (unformatResult instanceof VerificationFailed)
            return new VerificationFailed<>();

        else
            return new VerificationSucceeded<>();
    }

    private <A, P> LTL<APPrime<A, P>> convertLTL(LTL<P> ltl) {
        if (ltl instanceof And) {
            And<P> ltlAnd = (And) ltl;
            return LTL.and(convertLTL(ltlAnd.getLeft()), convertLTL(ltlAnd.getRight()));
        } else if (ltl instanceof AP) {
            AP<P> ltlAP = (AP) ltl;
            return new AP<>(new APPrime<>(ltlAP.getName()));
        } else if (ltl instanceof Next) {
            Next<P> ltlNext = (Next) ltl;
            return LTL.next(convertLTL(ltlNext.getInner()));
        } else if (ltl instanceof Not) {
            Not<P> ltl_not = (Not) ltl;
            return LTL.not(convertLTL(ltl_not.getInner()));
        } else if (ltl instanceof TRUE) {
            return new TRUE<>();
        } else if (ltl instanceof Until) {
            Until<P> ltl_until = (Until) ltl;
            return LTL.until(convertLTL(ltl_until.getLeft()), convertLTL(ltl_until.getRight()));
        } else {
            throw new IllegalArgumentException("Bad LTL convert with " + ltl);
        }
    }

    private <S, A, P> LTL<APPrime<A, P>> getUncond(Set<Set<A>> uncond) {

        LTL<APPrime<A, P>> currAnd = new TRUE<>();
        for (Set<A> actSet : uncond) {
            currAnd = LTL.and(currAnd, ltlAlways(ltlEventually(getUnariOr(actSet, "t"))));
        }
        return currAnd;
    }

    private <S, A, P> LTL<APPrime<A, P>> getStrong(Set<Set<A>> uncond) {

        LTL<APPrime<A, P>> currAnd = new TRUE<>();
        for (Set<A> actSet : uncond) {
            LTL<APPrime<A, P>> ifSide = ltlAlways(ltlEventually(getUnariOr(actSet, "e")));
            LTL<APPrime<A, P>> thenSide = ltlAlways(ltlEventually(getUnariOr(actSet, "t")));
            LTL<APPrime<A, P>> ifThen = ltlOr(new Not<>(ifSide), thenSide);
            currAnd = LTL.and(currAnd, ifThen);
        }
        return currAnd;
    }

    private <S, A, P> LTL<APPrime<A, P>> getWeak(Set<Set<A>> uncond) {

        LTL<APPrime<A, P>> currAnd = new TRUE<>();
        for (Set<A> actSet : uncond) {
            LTL<APPrime<A, P>> ifSide = ltlEventually(ltlAlways(getUnariOr(actSet, "e")));
            LTL<APPrime<A, P>> thenSide = ltlEventually(ltlAlways(getUnariOr(actSet, "t")));
            LTL<APPrime<A, P>> ifThen = ltlOr(new Not<>(ifSide), thenSide);
            currAnd = LTL.and(currAnd, ifThen);
        }
        return currAnd;
    }

    private <A, P> LTL<APPrime<A, P>> getUnariOr(Set<A> acts, String type) { // returns an unari Or on triggered/enabled(alpha) for each alpha in acts
        LTL<APPrime<A, P>> currOr = new TRUE<>();
        if (acts.isEmpty())
            return currOr;
        currOr = new Not<>(currOr);
        for (A act : acts) {// OR from all triggered/enabled
            APPrime<A, P> trig = new APPrime<>(act, (P) type);
            AP<APPrime<A, P>> myAP = new AP<>(trig);
            currOr = ltlOr(currOr, myAP);
        }
        return currOr;
    }

    private <L> Not<L> ltlOr(LTL<L> ltlRight, LTL<L> ltlLeft) {
        Not<L> ltlL = new Not<>(ltlLeft);
        Not<L> ltlR = new Not<>(ltlRight);
        And<L> ltlAnd = new And<L>(ltlL, ltlR);
        return new Not<L>(ltlAnd);
    }

    //always []a --> not <> not a
    private <L> LTL<L> ltlAlways(LTL<L> ltl) {
        Not<L> ltlNotA = new Not<>(ltl); // not a
        LTL<L> ev = ltlEventually(ltlNotA); // <> not a
        return new Not<>(ev); // not <> not a
    }

    // eventually <>a --> true U a
    private <L> LTL<L> ltlEventually(LTL<L> ltl) {
        TRUE<L> ltlTrue = new TRUE<L>();
        return new Until<>(ltlTrue, ltl);
    }
}

