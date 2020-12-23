%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:59 EST 2020

% Result     : CounterSatisfiable 3.52s
% Output     : Saturation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   95 (1758 expanded)
%              Number of clauses        :   41 ( 213 expanded)
%              Number of leaves         :   21 ( 550 expanded)
%              Depth                    :   17
%              Number of atoms          :  208 (2590 expanded)
%              Number of equality atoms :  155 (2307 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31])).

fof(f54,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f61])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f70,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f54,f62,f61])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f43,f36,f60,f62,f61])).

fof(f56,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f44,f57,f58,f61])).

fof(f55,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_69,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_68,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_87,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2646,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0)
    | ~ iProver_ARSWP_44 ),
    inference(arg_filter_abstr,[status(unp)],[c_14])).

cnf(c_2734,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2646])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2642,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_40
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_2738,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2642])).

cnf(c_2992,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_2738])).

cnf(c_9,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2644,plain,
    ( ~ iProver_ARSWP_42
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_2736,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_42 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_12,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2876,plain,
    ( ~ iProver_ARSWP_42
    | X0 = sK3
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_2877,plain,
    ( X0 = sK3
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_42 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2876])).

cnf(c_2879,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_42 != iProver_top ),
    inference(instantiation,[status(thm)],[c_2877])).

cnf(c_3069,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_42 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2736,c_12,c_2879])).

cnf(c_3075,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2992,c_3069])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3088,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3075,c_6])).

cnf(c_3202,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_2992])).

cnf(c_3200,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_3069])).

cnf(c_3654,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3202,c_3200])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2641,plain,
    ( ~ iProver_ARSWP_39
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2739,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_39 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2641])).

cnf(c_3076,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_2739])).

cnf(c_3080,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_6])).

cnf(c_3102,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_2739])).

cnf(c_3422,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3202,c_3102])).

cnf(c_3206,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_2734])).

cnf(c_3415,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_2738])).

cnf(c_3099,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_3069])).

cnf(c_3306,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_3102])).

cnf(c_3105,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_2734])).

cnf(c_13,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.52/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.99  
% 3.52/0.99  ------  iProver source info
% 3.52/0.99  
% 3.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.99  git: non_committed_changes: false
% 3.52/0.99  git: last_make_outside_of_git: false
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  ------ Parsing...
% 3.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  ------ Proving...
% 3.52/0.99  ------ Problem Properties 
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  clauses                                 12
% 3.52/0.99  conjectures                             3
% 3.52/0.99  EPR                                     2
% 3.52/0.99  Horn                                    11
% 3.52/0.99  unary                                   10
% 3.52/0.99  binary                                  1
% 3.52/0.99  lits                                    15
% 3.52/0.99  lits eq                                 13
% 3.52/0.99  fd_pure                                 0
% 3.52/0.99  fd_pseudo                               0
% 3.52/0.99  fd_cond                                 0
% 3.52/0.99  fd_pseudo_cond                          1
% 3.52/0.99  AC symbols                              0
% 3.52/0.99  
% 3.52/0.99  ------ Input Options Time Limit: Unbounded
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.52/0.99  Current options:
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  % SZS output start Saturation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  fof(f3,axiom,(
% 3.52/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f35,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.52/0.99    inference(cnf_transformation,[],[f3])).
% 3.52/0.99  
% 3.52/0.99  fof(f2,axiom,(
% 3.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f24,plain,(
% 3.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(rectify,[],[f2])).
% 3.52/0.99  
% 3.52/0.99  fof(f25,plain,(
% 3.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(ennf_transformation,[],[f24])).
% 3.52/0.99  
% 3.52/0.99  fof(f29,plain,(
% 3.52/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f30,plain,(
% 3.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).
% 3.52/0.99  
% 3.52/0.99  fof(f33,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f34,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f22,conjecture,(
% 3.52/0.99    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f23,negated_conjecture,(
% 3.52/0.99    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.52/0.99    inference(negated_conjecture,[],[f22])).
% 3.52/0.99  
% 3.52/0.99  fof(f28,plain,(
% 3.52/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.52/0.99    inference(ennf_transformation,[],[f23])).
% 3.52/0.99  
% 3.52/0.99  fof(f31,plain,(
% 3.52/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f32,plain,(
% 3.52/0.99    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31])).
% 3.52/0.99  
% 3.52/0.99  fof(f54,plain,(
% 3.52/0.99    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f15,axiom,(
% 3.52/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f47,plain,(
% 3.52/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f15])).
% 3.52/0.99  
% 3.52/0.99  fof(f62,plain,(
% 3.52/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f47,f61])).
% 3.52/0.99  
% 3.52/0.99  fof(f16,axiom,(
% 3.52/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f48,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f16])).
% 3.52/0.99  
% 3.52/0.99  fof(f17,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f49,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f17])).
% 3.52/0.99  
% 3.52/0.99  fof(f18,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f50,plain,(
% 3.52/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f18])).
% 3.52/0.99  
% 3.52/0.99  fof(f19,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f51,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f19])).
% 3.52/0.99  
% 3.52/0.99  fof(f20,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f52,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f20])).
% 3.52/0.99  
% 3.52/0.99  fof(f58,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f51,f52])).
% 3.52/0.99  
% 3.52/0.99  fof(f59,plain,(
% 3.52/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f50,f58])).
% 3.52/0.99  
% 3.52/0.99  fof(f60,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f49,f59])).
% 3.52/0.99  
% 3.52/0.99  fof(f61,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f48,f60])).
% 3.52/0.99  
% 3.52/0.99  fof(f70,plain,(
% 3.52/0.99    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 3.52/0.99    inference(definition_unfolding,[],[f54,f62,f61])).
% 3.52/0.99  
% 3.52/0.99  fof(f5,axiom,(
% 3.52/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f26,plain,(
% 3.52/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f5])).
% 3.52/0.99  
% 3.52/0.99  fof(f37,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f26])).
% 3.52/0.99  
% 3.52/0.99  fof(f11,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f27,plain,(
% 3.52/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.52/0.99    inference(ennf_transformation,[],[f11])).
% 3.52/0.99  
% 3.52/0.99  fof(f43,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.52/0.99    inference(cnf_transformation,[],[f27])).
% 3.52/0.99  
% 3.52/0.99  fof(f4,axiom,(
% 3.52/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f36,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f4])).
% 3.52/0.99  
% 3.52/0.99  fof(f67,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.52/0.99    inference(definition_unfolding,[],[f43,f36,f60,f62,f61])).
% 3.52/0.99  
% 3.52/0.99  fof(f56,plain,(
% 3.52/0.99    sK1 != sK3),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f7,axiom,(
% 3.52/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f39,plain,(
% 3.52/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.52/0.99    inference(cnf_transformation,[],[f7])).
% 3.52/0.99  
% 3.52/0.99  fof(f12,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f44,plain,(
% 3.52/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f12])).
% 3.52/0.99  
% 3.52/0.99  fof(f8,axiom,(
% 3.52/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f40,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f8])).
% 3.52/0.99  
% 3.52/0.99  fof(f57,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f40,f36])).
% 3.52/0.99  
% 3.52/0.99  fof(f64,plain,(
% 3.52/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f44,f57,f58,f61])).
% 3.52/0.99  
% 3.52/0.99  fof(f55,plain,(
% 3.52/0.99    sK1 != sK2),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f6,axiom,(
% 3.52/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f38,plain,(
% 3.52/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.52/0.99    inference(cnf_transformation,[],[f6])).
% 3.52/0.99  
% 3.52/0.99  cnf(c_69,plain,
% 3.52/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/0.99      theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_68,plain,
% 3.52/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/0.99      theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_87,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3,plain,
% 3.52/0.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2,plain,
% 3.52/0.99      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1,plain,
% 3.52/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_14,negated_conjecture,
% 3.52/0.99      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2646,negated_conjecture,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) | ~ iProver_ARSWP_44 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_14]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2734,plain,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2646]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2642,plain,
% 3.52/0.99      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.52/0.99      | ~ iProver_ARSWP_40
% 3.52/0.99      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2738,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.52/0.99      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2642]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2992,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2734,c_2738]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_9,plain,
% 3.52/0.99      ( X0 = X1
% 3.52/0.99      | X2 = X1
% 3.52/0.99      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2644,plain,
% 3.52/0.99      ( ~ iProver_ARSWP_42
% 3.52/0.99      | X0 = X1
% 3.52/0.99      | X2 = X1
% 3.52/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2736,plain,
% 3.52/0.99      ( X0 = X1
% 3.52/0.99      | X2 = X1
% 3.52/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12,negated_conjecture,
% 3.52/0.99      ( sK1 != sK3 ),
% 3.52/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2876,plain,
% 3.52/0.99      ( ~ iProver_ARSWP_42
% 3.52/0.99      | X0 = sK3
% 3.52/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | sK1 = sK3 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_2644]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2877,plain,
% 3.52/0.99      ( X0 = sK3
% 3.52/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | sK1 = sK3
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2876]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2879,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | sK1 = sK3
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_2877]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3069,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2736,c_12,c_2879]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3075,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2992,c_3069]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_6,plain,
% 3.52/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3088,plain,
% 3.52/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_3075,c_6]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3202,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3088,c_2992]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3200,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3088,c_3069]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3654,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3202,c_3200]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_0,plain,
% 3.52/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.52/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2641,plain,
% 3.52/0.99      ( ~ iProver_ARSWP_39
% 3.52/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2739,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2641]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3076,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3069,c_2739]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3080,plain,
% 3.52/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_3076,c_6]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3102,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3080,c_2739]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3422,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3202,c_3102]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3206,plain,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3088,c_2734]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3415,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3206,c_2738]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3099,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3080,c_3069]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3306,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3099,c_3102]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3105,plain,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_42 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3080,c_2734]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_13,negated_conjecture,
% 3.52/0.99      ( sK1 != sK2 ),
% 3.52/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5,plain,
% 3.52/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS output end Saturation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  ------                               Statistics
% 3.52/0.99  
% 3.52/0.99  ------ Selected
% 3.52/0.99  
% 3.52/0.99  total_time:                             0.15
% 3.52/0.99  
%------------------------------------------------------------------------------
