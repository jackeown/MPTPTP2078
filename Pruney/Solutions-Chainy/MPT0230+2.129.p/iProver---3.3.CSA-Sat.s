%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:59 EST 2020

% Result     : CounterSatisfiable 3.52s
% Output     : Saturation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   98 (2004 expanded)
%              Number of clauses        :   41 ( 213 expanded)
%              Number of leaves         :   22 ( 632 expanded)
%              Depth                    :   18
%              Number of atoms          :  211 (2836 expanded)
%              Number of equality atoms :  158 (2553 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34])).

fof(f60,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f19,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f68,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f79,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f60,f69,f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f50,f39,f67,f69,f68])).

fof(f62,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f51,f63,f64,f68])).

fof(f61,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_71,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_70,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_89,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2648,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0)
    | ~ iProver_ARSWP_44 ),
    inference(arg_filter_abstr,[status(unp)],[c_16])).

cnf(c_2736,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2648])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2644,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_40
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_2740,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_2994,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_2740])).

cnf(c_12,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2647,plain,
    ( ~ iProver_ARSWP_43
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_2737,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2878,plain,
    ( ~ iProver_ARSWP_43
    | X0 = sK3
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_2647])).

cnf(c_2879,plain,
    ( X0 = sK3
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2878])).

cnf(c_2881,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_43 != iProver_top ),
    inference(instantiation,[status(thm)],[c_2879])).

cnf(c_3071,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2737,c_14,c_2881])).

cnf(c_3077,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2994,c_3071])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3090,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3077,c_6])).

cnf(c_3190,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3090,c_2994])).

cnf(c_3188,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3090,c_3071])).

cnf(c_3672,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_3188])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2643,plain,
    ( ~ iProver_ARSWP_39
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2741,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0
    | iProver_ARSWP_39 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2643])).

cnf(c_3078,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3071,c_2741])).

cnf(c_3082,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3078,c_6])).

cnf(c_3104,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_2741])).

cnf(c_3405,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_3104])).

cnf(c_3194,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3090,c_2736])).

cnf(c_3398,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3194,c_2740])).

cnf(c_3101,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_3071])).

cnf(c_3315,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_3104])).

cnf(c_3107,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_2736])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:22 EST 2020
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
% 3.52/0.99  clauses                                 14
% 3.52/0.99  conjectures                             3
% 3.52/0.99  EPR                                     2
% 3.52/0.99  Horn                                    13
% 3.52/0.99  unary                                   12
% 3.52/0.99  binary                                  1
% 3.52/0.99  lits                                    17
% 3.52/0.99  lits eq                                 15
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
% 3.52/0.99  fof(f38,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.52/0.99    inference(cnf_transformation,[],[f3])).
% 3.52/0.99  
% 3.52/0.99  fof(f2,axiom,(
% 3.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f27,plain,(
% 3.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(rectify,[],[f2])).
% 3.52/0.99  
% 3.52/0.99  fof(f28,plain,(
% 3.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(ennf_transformation,[],[f27])).
% 3.52/0.99  
% 3.52/0.99  fof(f32,plain,(
% 3.52/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f33,plain,(
% 3.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f36,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f33])).
% 3.52/0.99  
% 3.52/0.99  fof(f37,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.52/0.99    inference(cnf_transformation,[],[f33])).
% 3.52/0.99  
% 3.52/0.99  fof(f25,conjecture,(
% 3.52/0.99    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f26,negated_conjecture,(
% 3.52/0.99    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.52/0.99    inference(negated_conjecture,[],[f25])).
% 3.52/0.99  
% 3.52/0.99  fof(f31,plain,(
% 3.52/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.52/0.99    inference(ennf_transformation,[],[f26])).
% 3.52/0.99  
% 3.52/0.99  fof(f34,plain,(
% 3.52/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f35,plain,(
% 3.52/0.99    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34])).
% 3.52/0.99  
% 3.52/0.99  fof(f60,plain,(
% 3.52/0.99    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.52/0.99    inference(cnf_transformation,[],[f35])).
% 3.52/0.99  
% 3.52/0.99  fof(f18,axiom,(
% 3.52/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f53,plain,(
% 3.52/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f18])).
% 3.52/0.99  
% 3.52/0.99  fof(f69,plain,(
% 3.52/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f53,f68])).
% 3.52/0.99  
% 3.52/0.99  fof(f19,axiom,(
% 3.52/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f54,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f19])).
% 3.52/0.99  
% 3.52/0.99  fof(f20,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f55,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f20])).
% 3.52/0.99  
% 3.52/0.99  fof(f21,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f56,plain,(
% 3.52/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f21])).
% 3.52/0.99  
% 3.52/0.99  fof(f22,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f57,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f22])).
% 3.52/0.99  
% 3.52/0.99  fof(f23,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f58,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f23])).
% 3.52/0.99  
% 3.52/0.99  fof(f24,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f59,plain,(
% 3.52/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f24])).
% 3.52/0.99  
% 3.52/0.99  fof(f64,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f58,f59])).
% 3.52/0.99  
% 3.52/0.99  fof(f65,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f57,f64])).
% 3.52/0.99  
% 3.52/0.99  fof(f66,plain,(
% 3.52/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f56,f65])).
% 3.52/0.99  
% 3.52/0.99  fof(f67,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f55,f66])).
% 3.52/0.99  
% 3.52/0.99  fof(f68,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f54,f67])).
% 3.52/0.99  
% 3.52/0.99  fof(f79,plain,(
% 3.52/0.99    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 3.52/0.99    inference(definition_unfolding,[],[f60,f69,f68])).
% 3.52/0.99  
% 3.52/0.99  fof(f5,axiom,(
% 3.52/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f29,plain,(
% 3.52/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f5])).
% 3.52/0.99  
% 3.52/0.99  fof(f40,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f29])).
% 3.52/0.99  
% 3.52/0.99  fof(f15,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f30,plain,(
% 3.52/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.52/0.99    inference(ennf_transformation,[],[f15])).
% 3.52/0.99  
% 3.52/0.99  fof(f50,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f4,axiom,(
% 3.52/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f39,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f4])).
% 3.52/0.99  
% 3.52/0.99  fof(f77,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.52/0.99    inference(definition_unfolding,[],[f50,f39,f67,f69,f68])).
% 3.52/0.99  
% 3.52/0.99  fof(f62,plain,(
% 3.52/0.99    sK1 != sK3),
% 3.52/0.99    inference(cnf_transformation,[],[f35])).
% 3.52/0.99  
% 3.52/0.99  fof(f7,axiom,(
% 3.52/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f42,plain,(
% 3.52/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.52/0.99    inference(cnf_transformation,[],[f7])).
% 3.52/0.99  
% 3.52/0.99  fof(f16,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f51,plain,(
% 3.52/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f16])).
% 3.52/0.99  
% 3.52/0.99  fof(f8,axiom,(
% 3.52/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f43,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f8])).
% 3.52/0.99  
% 3.52/0.99  fof(f63,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f43,f39])).
% 3.52/0.99  
% 3.52/0.99  fof(f71,plain,(
% 3.52/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f51,f63,f64,f68])).
% 3.52/0.99  
% 3.52/0.99  fof(f61,plain,(
% 3.52/0.99    sK1 != sK2),
% 3.52/0.99    inference(cnf_transformation,[],[f35])).
% 3.52/0.99  
% 3.52/0.99  fof(f6,axiom,(
% 3.52/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f41,plain,(
% 3.52/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.52/0.99    inference(cnf_transformation,[],[f6])).
% 3.52/0.99  
% 3.52/0.99  cnf(c_71,plain,
% 3.52/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/0.99      theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_70,plain,
% 3.52/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/0.99      theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_89,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3,plain,
% 3.52/0.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2,plain,
% 3.52/0.99      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1,plain,
% 3.52/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_16,negated_conjecture,
% 3.52/0.99      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2648,negated_conjecture,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) | ~ iProver_ARSWP_44 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_16]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2736,plain,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) = iProver_top
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2648]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2644,plain,
% 3.52/0.99      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.52/0.99      | ~ iProver_ARSWP_40
% 3.52/0.99      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2740,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.52/0.99      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2994,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2736,c_2740]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12,plain,
% 3.52/0.99      ( X0 = X1
% 3.52/0.99      | X2 = X1
% 3.52/0.99      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2647,plain,
% 3.52/0.99      ( ~ iProver_ARSWP_43
% 3.52/0.99      | X0 = X1
% 3.52/0.99      | X2 = X1
% 3.52/0.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2737,plain,
% 3.52/0.99      ( X0 = X1
% 3.52/0.99      | X2 = X1
% 3.52/0.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_14,negated_conjecture,
% 3.52/0.99      ( sK1 != sK3 ),
% 3.52/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2878,plain,
% 3.52/0.99      ( ~ iProver_ARSWP_43
% 3.52/0.99      | X0 = sK3
% 3.52/0.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | sK1 = sK3 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_2647]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2879,plain,
% 3.52/0.99      ( X0 = sK3
% 3.52/0.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | sK1 = sK3
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2878]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2881,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | sK1 = sK3
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_2879]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3071,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2737,c_14,c_2881]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3077,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2994,c_3071]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_6,plain,
% 3.52/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3090,plain,
% 3.52/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_3077,c_6]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3190,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3090,c_2994]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3188,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3090,c_3071]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3672,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3190,c_3188]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_0,plain,
% 3.52/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.52/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2643,plain,
% 3.52/0.99      ( ~ iProver_ARSWP_39
% 3.52/0.99      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0 ),
% 3.52/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2741,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_2643]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3078,plain,
% 3.52/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3071,c_2741]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3082,plain,
% 3.52/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_3078,c_6]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3104,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3082,c_2741]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3405,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3190,c_3104]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3194,plain,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3090,c_2736]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3398,plain,
% 3.52/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3194,c_2740]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3101,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3082,c_3071]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3315,plain,
% 3.52/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3101,c_3104]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3107,plain,
% 3.52/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.52/0.99      | iProver_ARSWP_44 != iProver_top
% 3.52/0.99      | iProver_ARSWP_43 != iProver_top
% 3.52/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_3082,c_2736]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_15,negated_conjecture,
% 3.52/0.99      ( sK1 != sK2 ),
% 3.52/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5,plain,
% 3.52/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS output end Saturation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  ------                               Statistics
% 3.52/0.99  
% 3.52/0.99  ------ Selected
% 3.52/0.99  
% 3.52/0.99  total_time:                             0.154
% 3.52/0.99  
%------------------------------------------------------------------------------
