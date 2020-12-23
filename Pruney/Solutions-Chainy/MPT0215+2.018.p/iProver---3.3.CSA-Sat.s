%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:56 EST 2020

% Result     : CounterSatisfiable 3.63s
% Output     : Saturation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  109 (1225 expanded)
%              Number of clauses        :   55 ( 189 expanded)
%              Number of leaves         :   20 ( 372 expanded)
%              Depth                    :   17
%              Number of atoms          :  247 (1867 expanded)
%              Number of equality atoms :  210 (1759 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f51,f40,f68,f71,f69])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X1,X2) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f25])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k2_tarski(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k2_tarski(X1,X2) = k1_tarski(X0) )
   => ( sK0 != sK1
      & k2_tarski(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK0 != sK1
    & k2_tarski(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34])).

fof(f63,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f45,f64,f66,f66])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_59,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_12,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2082,plain,
    ( ~ iProver_ARSWP_50
    | X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_2221,plain,
    ( X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_50 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2082])).

cnf(c_16,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2601,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK0 != X1
    | iProver_ARSWP_50 != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_16])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_28,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_32,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_92,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_435,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_436,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_2607,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = X0
    | sK0 != X1
    | iProver_ARSWP_50 != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_16])).

cnf(c_2798,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = sK0
    | sK0 != sK0
    | iProver_ARSWP_50 != iProver_top ),
    inference(instantiation,[status(thm)],[c_2607])).

cnf(c_2912,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_50 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2601,c_16,c_28,c_32,c_436,c_2798])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2079,plain,
    ( ~ iProver_ARSWP_47
    | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_2224,plain,
    ( arAF0_k5_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_47 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2079])).

cnf(c_2617,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X0
    | iProver_ARSWP_50 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2221])).

cnf(c_3041,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(superposition,[status(thm)],[c_2224,c_2617])).

cnf(c_3421,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3041])).

cnf(c_3557,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(superposition,[status(thm)],[c_3421,c_3421])).

cnf(c_3684,plain,
    ( arAF0_k5_enumset1_0 != X0
    | k1_xboole_0 = X0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3557])).

cnf(c_3994,plain,
    ( arAF0_k5_xboole_0_0 != X0
    | k1_xboole_0 = X0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_3684])).

cnf(c_3683,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | k1_xboole_0 != X0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3557])).

cnf(c_3708,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3683,c_3557])).

cnf(c_2618,plain,
    ( arAF0_k5_enumset1_0 != X0
    | arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_50 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2221])).

cnf(c_3858,plain,
    ( arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(superposition,[status(thm)],[c_3708,c_2618])).

cnf(c_2620,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 != X1
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_50 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2221])).

cnf(c_3857,plain,
    ( X0 = X1
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(superposition,[status(thm)],[c_3708,c_2620])).

cnf(c_3685,plain,
    ( arAF0_k5_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3557])).

cnf(c_2619,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_50 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2221])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2075,plain,
    ( ~ iProver_ARSWP_43
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2228,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2075])).

cnf(c_2599,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_2228])).

cnf(c_2612,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_50 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2221])).

cnf(c_2762,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2599,c_2612])).

cnf(c_91,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2380,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_92,c_91])).

cnf(c_2465,plain,
    ( ~ iProver_ARSWP_43
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_2380,c_2075])).

cnf(c_2466,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2465])).

cnf(c_3364,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2762,c_2466])).

cnf(c_6,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2078,plain,
    ( arAF0_r1_xboole_0_0_1(k1_xboole_0)
    | ~ iProver_ARSWP_46 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_2225,plain,
    ( arAF0_r1_xboole_0_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2078])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2077,plain,
    ( ~ arAF0_r1_xboole_0_0_1(X0)
    | ~ iProver_ARSWP_45
    | k1_xboole_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_2226,plain,
    ( k1_xboole_0 = X0
    | arAF0_r1_xboole_0_0_1(X0) != iProver_top
    | iProver_ARSWP_45 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2076,plain,
    ( ~ iProver_ARSWP_44
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_2227,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_44 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2076])).

cnf(c_2230,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2229,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:52:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.63/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.99  
% 3.63/0.99  ------  iProver source info
% 3.63/0.99  
% 3.63/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.99  git: non_committed_changes: false
% 3.63/0.99  git: last_make_outside_of_git: false
% 3.63/0.99  
% 3.63/0.99  ------ 
% 3.63/0.99  ------ Parsing...
% 3.63/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  ------ Proving...
% 3.63/0.99  ------ Problem Properties 
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  clauses                                 17
% 3.63/0.99  conjectures                             2
% 3.63/0.99  EPR                                     5
% 3.63/0.99  Horn                                    16
% 3.63/0.99  unary                                   14
% 3.63/0.99  binary                                  1
% 3.63/0.99  lits                                    22
% 3.63/0.99  lits eq                                 17
% 3.63/0.99  fd_pure                                 0
% 3.63/0.99  fd_pseudo                               0
% 3.63/0.99  fd_cond                                 1
% 3.63/0.99  fd_pseudo_cond                          2
% 3.63/0.99  AC symbols                              0
% 3.63/0.99  
% 3.63/0.99  ------ Input Options Time Limit: Unbounded
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.63/0.99  Current options:
% 3.63/0.99  ------ 
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  % SZS output start Saturation for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  fof(f14,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f30,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.63/0.99    inference(ennf_transformation,[],[f14])).
% 3.63/0.99  
% 3.63/0.99  fof(f51,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.63/0.99    inference(cnf_transformation,[],[f30])).
% 3.63/0.99  
% 3.63/0.99  fof(f3,axiom,(
% 3.63/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f40,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f3])).
% 3.63/0.99  
% 3.63/0.99  fof(f18,axiom,(
% 3.63/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f55,plain,(
% 3.63/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f18])).
% 3.63/0.99  
% 3.63/0.99  fof(f71,plain,(
% 3.63/0.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f55,f69])).
% 3.63/0.99  
% 3.63/0.99  fof(f19,axiom,(
% 3.63/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f56,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f19])).
% 3.63/0.99  
% 3.63/0.99  fof(f20,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f57,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f20])).
% 3.63/0.99  
% 3.63/0.99  fof(f21,axiom,(
% 3.63/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f58,plain,(
% 3.63/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f21])).
% 3.63/0.99  
% 3.63/0.99  fof(f22,axiom,(
% 3.63/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f59,plain,(
% 3.63/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f22])).
% 3.63/0.99  
% 3.63/0.99  fof(f23,axiom,(
% 3.63/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f60,plain,(
% 3.63/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f65,plain,(
% 3.63/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f59,f60])).
% 3.63/0.99  
% 3.63/0.99  fof(f66,plain,(
% 3.63/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f58,f65])).
% 3.63/0.99  
% 3.63/0.99  fof(f68,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f57,f66])).
% 3.63/0.99  
% 3.63/0.99  fof(f69,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f56,f68])).
% 3.63/0.99  
% 3.63/0.99  fof(f77,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.63/0.99    inference(definition_unfolding,[],[f51,f40,f68,f71,f69])).
% 3.63/0.99  
% 3.63/0.99  fof(f25,conjecture,(
% 3.63/0.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f26,negated_conjecture,(
% 3.63/0.99    ~! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 3.63/0.99    inference(negated_conjecture,[],[f25])).
% 3.63/0.99  
% 3.63/0.99  fof(f31,plain,(
% 3.63/0.99    ? [X0,X1,X2] : (X0 != X1 & k2_tarski(X1,X2) = k1_tarski(X0))),
% 3.63/0.99    inference(ennf_transformation,[],[f26])).
% 3.63/0.99  
% 3.63/0.99  fof(f34,plain,(
% 3.63/0.99    ? [X0,X1,X2] : (X0 != X1 & k2_tarski(X1,X2) = k1_tarski(X0)) => (sK0 != sK1 & k2_tarski(sK1,sK2) = k1_tarski(sK0))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f35,plain,(
% 3.63/0.99    sK0 != sK1 & k2_tarski(sK1,sK2) = k1_tarski(sK0)),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34])).
% 3.63/0.99  
% 3.63/0.99  fof(f63,plain,(
% 3.63/0.99    sK0 != sK1),
% 3.63/0.99    inference(cnf_transformation,[],[f35])).
% 3.63/0.99  
% 3.63/0.99  fof(f2,axiom,(
% 3.63/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f32,plain,(
% 3.63/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/0.99    inference(nnf_transformation,[],[f2])).
% 3.63/0.99  
% 3.63/0.99  fof(f33,plain,(
% 3.63/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/0.99    inference(flattening,[],[f32])).
% 3.63/0.99  
% 3.63/0.99  fof(f37,plain,(
% 3.63/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.63/0.99    inference(cnf_transformation,[],[f33])).
% 3.63/0.99  
% 3.63/0.99  fof(f83,plain,(
% 3.63/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.63/0.99    inference(equality_resolution,[],[f37])).
% 3.63/0.99  
% 3.63/0.99  fof(f39,plain,(
% 3.63/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f33])).
% 3.63/0.99  
% 3.63/0.99  fof(f6,axiom,(
% 3.63/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f43,plain,(
% 3.63/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.63/0.99    inference(cnf_transformation,[],[f6])).
% 3.63/0.99  
% 3.63/0.99  fof(f24,axiom,(
% 3.63/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f61,plain,(
% 3.63/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f24])).
% 3.63/0.99  
% 3.63/0.99  fof(f8,axiom,(
% 3.63/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f45,plain,(
% 3.63/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f8])).
% 3.63/0.99  
% 3.63/0.99  fof(f7,axiom,(
% 3.63/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f44,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f7])).
% 3.63/0.99  
% 3.63/0.99  fof(f64,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f44,f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f67,plain,(
% 3.63/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f45,f64,f66,f66])).
% 3.63/0.99  
% 3.63/0.99  fof(f72,plain,(
% 3.63/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f61,f67])).
% 3.63/0.99  
% 3.63/0.99  fof(f4,axiom,(
% 3.63/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f29,plain,(
% 3.63/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.63/0.99    inference(ennf_transformation,[],[f4])).
% 3.63/0.99  
% 3.63/0.99  fof(f41,plain,(
% 3.63/0.99    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f29])).
% 3.63/0.99  
% 3.63/0.99  fof(f84,plain,(
% 3.63/0.99    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.63/0.99    inference(equality_resolution,[],[f41])).
% 3.63/0.99  
% 3.63/0.99  fof(f42,plain,(
% 3.63/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.63/0.99    inference(cnf_transformation,[],[f29])).
% 3.63/0.99  
% 3.63/0.99  fof(f1,axiom,(
% 3.63/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f27,plain,(
% 3.63/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.63/0.99    inference(rectify,[],[f1])).
% 3.63/0.99  
% 3.63/0.99  fof(f36,plain,(
% 3.63/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.63/0.99    inference(cnf_transformation,[],[f27])).
% 3.63/0.99  
% 3.63/0.99  cnf(c_59,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | X2 = X1
% 3.63/0.99      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 3.63/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2082,plain,
% 3.63/0.99      ( ~ iProver_ARSWP_50
% 3.63/0.99      | X0 = X1
% 3.63/0.99      | X2 = X1
% 3.63/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.63/0.99      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2221,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | X2 = X1
% 3.63/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2082]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_16,negated_conjecture,
% 3.63/0.99      ( sK0 != sK1 ),
% 3.63/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2601,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | sK0 != X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2221,c_16]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f83]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_28,plain,
% 3.63/0.99      ( r1_tarski(sK0,sK0) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2,plain,
% 3.63/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.63/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_32,plain,
% 3.63/0.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_92,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_435,plain,
% 3.63/0.99      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_92]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_436,plain,
% 3.63/0.99      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_435]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2607,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | sK1 = X0
% 3.63/0.99      | sK0 != X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2221,c_16]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2798,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | sK1 = sK0
% 3.63/0.99      | sK0 != sK0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_2607]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2912,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_2601,c_16,c_28,c_32,c_436,c_2798]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_7,plain,
% 3.63/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2079,plain,
% 3.63/0.99      ( ~ iProver_ARSWP_47 | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
% 3.63/0.99      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2224,plain,
% 3.63/0.99      ( arAF0_k5_xboole_0_0 = k1_xboole_0 | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2079]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2617,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.63/0.99      | arAF0_k5_enumset1_0 = X1
% 3.63/0.99      | arAF0_k5_xboole_0_0 != X0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_2221]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3041,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.63/0.99      | arAF0_k5_enumset1_0 = X1
% 3.63/0.99      | k1_xboole_0 != X0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2224,c_2617]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3421,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.63/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(equality_resolution,[status(thm)],[c_3041]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3557,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_3421,c_3421]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3684,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 != X0
% 3.63/0.99      | k1_xboole_0 = X0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_3557]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3994,plain,
% 3.63/0.99      ( arAF0_k5_xboole_0_0 != X0
% 3.63/0.99      | k1_xboole_0 = X0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2912,c_3684]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3683,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.63/0.99      | k1_xboole_0 != X0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_3557]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3708,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3683,c_3557]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2618,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 != X0
% 3.63/0.99      | arAF0_k5_xboole_0_0 = X0
% 3.63/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_2221]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3858,plain,
% 3.63/0.99      ( arAF0_k5_xboole_0_0 = X0
% 3.63/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.63/0.99      | k1_xboole_0 != X0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_3708,c_2618]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2620,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_enumset1_0 != X1
% 3.63/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_2221]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3857,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.63/0.99      | k1_xboole_0 != X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_3708,c_2620]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3685,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.63/0.99      | k1_xboole_0 != X0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_47 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_3557]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2619,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_enumset1_0 = X1
% 3.63/0.99      | arAF0_k5_xboole_0_0 != X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_2221]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_0,plain,
% 3.63/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.63/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2075,plain,
% 3.63/0.99      ( ~ iProver_ARSWP_43 | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.63/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2228,plain,
% 3.63/0.99      ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.63/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2075]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2599,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2221,c_2228]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2612,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | arAF0_k5_xboole_0_0 != X1
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_2221]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2762,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | iProver_ARSWP_50 != iProver_top
% 3.63/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2599,c_2612]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_91,plain,( X0 = X0 ),theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2380,plain,
% 3.63/0.99      ( X0 != X1 | X1 = X0 ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_92,c_91]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2465,plain,
% 3.63/0.99      ( ~ iProver_ARSWP_43 | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_2380,c_2075]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2466,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2465]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3364,plain,
% 3.63/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.63/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.63/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2762,c_2466]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_6,plain,
% 3.63/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2078,plain,
% 3.63/0.99      ( arAF0_r1_xboole_0_0_1(k1_xboole_0) | ~ iProver_ARSWP_46 ),
% 3.63/0.99      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2225,plain,
% 3.63/0.99      ( arAF0_r1_xboole_0_0_1(k1_xboole_0) = iProver_top
% 3.63/0.99      | iProver_ARSWP_46 != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2078]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_5,plain,
% 3.63/0.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2077,plain,
% 3.63/0.99      ( ~ arAF0_r1_xboole_0_0_1(X0) | ~ iProver_ARSWP_45 | k1_xboole_0 = X0 ),
% 3.63/0.99      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2226,plain,
% 3.63/0.99      ( k1_xboole_0 = X0
% 3.63/0.99      | arAF0_r1_xboole_0_0_1(X0) != iProver_top
% 3.63/0.99      | iProver_ARSWP_45 != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1,plain,
% 3.63/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2076,plain,
% 3.63/0.99      ( ~ iProver_ARSWP_44 | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.63/0.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2227,plain,
% 3.63/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0 | iProver_ARSWP_44 != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2076]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2230,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.63/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2229,plain,
% 3.63/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  % SZS output end Saturation for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  ------                               Statistics
% 3.63/0.99  
% 3.63/0.99  ------ Selected
% 3.63/0.99  
% 3.63/0.99  total_time:                             0.141
% 3.63/0.99  
%------------------------------------------------------------------------------
