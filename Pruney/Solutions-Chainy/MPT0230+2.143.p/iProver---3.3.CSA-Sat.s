%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:01 EST 2020

% Result     : CounterSatisfiable 14.93s
% Output     : Saturation 14.93s
% Verified   : 
% Statistics : Number of formulae       :  262 (55089 expanded)
%              Number of clauses        :  211 (8340 expanded)
%              Number of leaves         :   18 (17317 expanded)
%              Depth                    :   22
%              Number of atoms          :  937 (85526 expanded)
%              Number of equality atoms :  915 (77239 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    6 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f41,f32,f57,f59,f58])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK0 != sK2
      & sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK0 != sK2
    & sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f54,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f55,f48,f59])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f37,f55,f48,f48])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f43,f55,f59,f61,f56])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2))))))) ),
    inference(definition_unfolding,[],[f44,f55,f61,f59,f56])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f52,f59,f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_35,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3033,plain,
    ( ~ iProver_ARSWP_43
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_3138,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3033])).

cnf(c_10,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3290,plain,
    ( ~ iProver_ARSWP_43
    | X0 = sK2
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3033])).

cnf(c_3291,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | sK0 = sK2
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3290])).

cnf(c_3293,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | sK0 = sK2
    | iProver_ARSWP_43 != iProver_top ),
    inference(instantiation,[status(thm)],[c_3291])).

cnf(c_3555,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_10,c_3293])).

cnf(c_0,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3030,plain,
    ( ~ iProver_ARSWP_40
    | k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_3141,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_40 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3030])).

cnf(c_3565,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_3141])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3569,plain,
    ( arAF0_k3_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3565,c_3])).

cnf(c_3607,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_3555])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_enumset1(X0,X0,X0,X0,X0)))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3034,plain,
    ( ~ iProver_ARSWP_44
    | k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_3137,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3034])).

cnf(c_4136,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_3137])).

cnf(c_4168,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4136,c_3])).

cnf(c_4543,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_4168])).

cnf(c_4545,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_3137])).

cnf(c_14559,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_4545])).

cnf(c_26050,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_14559])).

cnf(c_3618,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_3141])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2))))))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3035,plain,
    ( ~ iProver_ARSWP_45
    | k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_3136,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3035])).

cnf(c_3612,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_3136])).

cnf(c_6533,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_3612])).

cnf(c_3563,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_3136])).

cnf(c_3576,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3563,c_3])).

cnf(c_4299,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_3576])).

cnf(c_4364,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4299,c_3])).

cnf(c_4308,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3576,c_3136])).

cnf(c_7340,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_4364,c_4308])).

cnf(c_19429,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_6533,c_7340])).

cnf(c_19440,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_6533,c_3136])).

cnf(c_25339,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_19440])).

cnf(c_25513,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_19429,c_25339])).

cnf(c_11467,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_4168])).

cnf(c_4548,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_3136])).

cnf(c_14925,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_4548])).

cnf(c_24793,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_11467,c_14925])).

cnf(c_4141,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_3137])).

cnf(c_11391,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_4141])).

cnf(c_23175,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_11391])).

cnf(c_24271,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_23175])).

cnf(c_7343,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_4308])).

cnf(c_18835,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_3136])).

cnf(c_22898,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_18835])).

cnf(c_23670,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_22898])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_23675,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_23670,c_2])).

cnf(c_23170,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_11391])).

cnf(c_23255,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_23170,c_3])).

cnf(c_23188,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_11391,c_3137])).

cnf(c_23192,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_11391,c_3141])).

cnf(c_23186,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_11391,c_4168])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3036,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k3_enumset1_0)
    | ~ iProver_ARSWP_46 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_3135,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k3_enumset1_0) = iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3036])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3031,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_41
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_3140,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3031])).

cnf(c_3403,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3135,c_3140])).

cnf(c_3561,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_3555])).

cnf(c_3595,plain,
    ( arAF0_k3_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3561,c_3])).

cnf(c_3479,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_3136])).

cnf(c_3481,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3479,c_2,c_3])).

cnf(c_3725,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3481])).

cnf(c_3728,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3136])).

cnf(c_8715,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3725,c_3728])).

cnf(c_15979,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_7340])).

cnf(c_15990,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_3136])).

cnf(c_21791,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_15990])).

cnf(c_22078,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_15979,c_21791])).

cnf(c_7348,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_4308])).

cnf(c_7353,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7348,c_2])).

cnf(c_18829,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_7353])).

cnf(c_20958,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_18829,c_3612])).

cnf(c_20950,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_18829,c_4141])).

cnf(c_3733,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3403])).

cnf(c_7347,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_4308])).

cnf(c_7363,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7347,c_2])).

cnf(c_18827,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_7363])).

cnf(c_20095,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_18827,c_3728])).

cnf(c_20206,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_20095])).

cnf(c_3723,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3555])).

cnf(c_20204,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3723,c_20095])).

cnf(c_4140,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3137])).

cnf(c_20093,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_18827,c_4140])).

cnf(c_19421,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_6533])).

cnf(c_19506,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_19421,c_3])).

cnf(c_19441,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_6533,c_3141])).

cnf(c_19436,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_6533,c_3576])).

cnf(c_19435,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_6533,c_7353])).

cnf(c_19427,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_6533,c_7343])).

cnf(c_18815,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_7343])).

cnf(c_18956,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_18815,c_3])).

cnf(c_18832,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_3137])).

cnf(c_18836,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_3141])).

cnf(c_18834,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_3481])).

cnf(c_18831,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_3576])).

cnf(c_18830,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_4168])).

cnf(c_5077,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_3725])).

cnf(c_8723,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_3728])).

cnf(c_9884,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_5077,c_8723])).

cnf(c_18826,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_9884])).

cnf(c_3737,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3135])).

cnf(c_3924,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3737,c_3140])).

cnf(c_8722,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3924,c_3728])).

cnf(c_8739,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8722,c_2])).

cnf(c_9154,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_8739])).

cnf(c_10169,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_9154])).

cnf(c_10221,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_10169,c_8723])).

cnf(c_18825,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_10221])).

cnf(c_18823,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_7340])).

cnf(c_18822,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7343,c_8715])).

cnf(c_10617,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_9884,c_7363])).

cnf(c_14631,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_10617,c_3728])).

cnf(c_18478,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_14631])).

cnf(c_9514,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7363,c_3136])).

cnf(c_18418,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_9514])).

cnf(c_10958,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_10221,c_3136])).

cnf(c_18259,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_10958])).

cnf(c_10625,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_9884,c_3136])).

cnf(c_18162,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_10625])).

cnf(c_4541,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_4168])).

cnf(c_4615,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4541,c_2,c_3])).

cnf(c_4894,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_4615])).

cnf(c_8829,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_4894,c_4140])).

cnf(c_17162,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8829,c_4168])).

cnf(c_17844,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_17162])).

cnf(c_8836,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3924,c_4140])).

cnf(c_8853,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8836,c_2])).

cnf(c_17156,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8829,c_8853])).

cnf(c_17346,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_17156])).

cnf(c_17149,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_8829])).

cnf(c_17246,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_17149,c_3])).

cnf(c_17152,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_8829])).

cnf(c_17235,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(demodulation,[status(thm)],[c_17152,c_2,c_3])).

cnf(c_17164,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8829,c_3137])).

cnf(c_7409,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_7353,c_3136])).

cnf(c_16933,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_7409])).

cnf(c_15989,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_3481])).

cnf(c_15986,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_3576])).

cnf(c_15984,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_8739])).

cnf(c_15983,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_7363])).

cnf(c_15982,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_9884])).

cnf(c_15981,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8715,c_10221])).

cnf(c_4542,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_4168])).

cnf(c_6268,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4542])).

cnf(c_6317,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_6268])).

cnf(c_14568,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4545])).

cnf(c_15222,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_6317,c_14568])).

cnf(c_6315,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3723,c_6268])).

cnf(c_15221,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_6315,c_14568])).

cnf(c_10950,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_10221,c_7363])).

cnf(c_14863,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_10950,c_3728])).

cnf(c_8709,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_3728])).

cnf(c_12514,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_8709])).

cnf(c_12502,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_6317,c_8709])).

cnf(c_11455,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_7340])).

cnf(c_11577,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_11455,c_3])).

cnf(c_11472,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_3136])).

cnf(c_11469,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_3137])).

cnf(c_11473,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_3141])).

cnf(c_11471,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_3481])).

cnf(c_11468,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_3576])).

cnf(c_11466,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_7353])).

cnf(c_11464,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_7363])).

cnf(c_11463,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_9884])).

cnf(c_11462,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_10221])).

cnf(c_11394,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_4141])).

cnf(c_4538,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_4168])).

cnf(c_4624,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4538,c_3])).

cnf(c_4641,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_4624])).

cnf(c_11390,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_4641,c_4141])).

cnf(c_11063,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_8853,c_3137])).

cnf(c_10949,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_10221,c_9884])).

cnf(c_10624,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_9884,c_3481])).

cnf(c_10621,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_9884,c_3576])).

cnf(c_10618,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_9884,c_8739])).

cnf(c_8837,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4140])).

cnf(c_8835,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3723,c_4140])).

cnf(c_8827,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_4140])).

cnf(c_4303,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3576])).

cnf(c_8710,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_4303,c_3728])).

cnf(c_7647,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_6315,c_6317])).

cnf(c_7401,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_7353])).

cnf(c_7454,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7401,c_3])).

cnf(c_4304,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_3576])).

cnf(c_6956,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_4304,c_3612])).

cnf(c_6049,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4303])).

cnf(c_5892,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4894])).

cnf(c_5706,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_4641])).

cnf(c_5540,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_3618])).

cnf(c_5537,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_3618])).

cnf(c_4640,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_4624])).

cnf(c_5266,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4640])).

cnf(c_5264,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3723,c_4640])).

cnf(c_4898,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4615])).

cnf(c_4644,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_4624])).

cnf(c_4549,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_3141])).

cnf(c_4544,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_3576])).

cnf(c_4305,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3576,c_3137])).

cnf(c_4023,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_41 != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_3723])).

cnf(c_3621,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_3135])).

cnf(c_11,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 14.93/3.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.93/3.05  
% 14.93/3.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.93/3.05  
% 14.93/3.05  ------  iProver source info
% 14.93/3.05  
% 14.93/3.05  git: date: 2020-06-30 10:37:57 +0100
% 14.93/3.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.93/3.05  git: non_committed_changes: false
% 14.93/3.05  git: last_make_outside_of_git: false
% 14.93/3.05  
% 14.93/3.05  ------ 
% 14.93/3.05  ------ Parsing...
% 14.93/3.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  ------ Proving...
% 14.93/3.05  ------ Problem Properties 
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  clauses                                 13
% 14.93/3.05  conjectures                             3
% 14.93/3.05  EPR                                     2
% 14.93/3.05  Horn                                    12
% 14.93/3.05  unary                                   11
% 14.93/3.05  binary                                  1
% 14.93/3.05  lits                                    16
% 14.93/3.05  lits eq                                 14
% 14.93/3.05  fd_pure                                 0
% 14.93/3.05  fd_pseudo                               0
% 14.93/3.05  fd_cond                                 0
% 14.93/3.05  fd_pseudo_cond                          1
% 14.93/3.05  AC symbols                              0
% 14.93/3.05  
% 14.93/3.05  ------ Input Options Time Limit: Unbounded
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 14.93/3.05  Current options:
% 14.93/3.05  ------ 
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/3.05  
% 14.93/3.05  ------ Proving...
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  % SZS status CounterSatisfiable for theBenchmark.p
% 14.93/3.05  
% 14.93/3.05  % SZS output start Saturation for theBenchmark.p
% 14.93/3.05  
% 14.93/3.05  fof(f12,axiom,(
% 14.93/3.05    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f28,plain,(
% 14.93/3.05    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 14.93/3.05    inference(ennf_transformation,[],[f12])).
% 14.93/3.05  
% 14.93/3.05  fof(f41,plain,(
% 14.93/3.05    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 14.93/3.05    inference(cnf_transformation,[],[f28])).
% 14.93/3.05  
% 14.93/3.05  fof(f2,axiom,(
% 14.93/3.05    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f32,plain,(
% 14.93/3.05    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f2])).
% 14.93/3.05  
% 14.93/3.05  fof(f16,axiom,(
% 14.93/3.05    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f45,plain,(
% 14.93/3.05    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f16])).
% 14.93/3.05  
% 14.93/3.05  fof(f59,plain,(
% 14.93/3.05    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 14.93/3.05    inference(definition_unfolding,[],[f45,f58])).
% 14.93/3.05  
% 14.93/3.05  fof(f17,axiom,(
% 14.93/3.05    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f46,plain,(
% 14.93/3.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f17])).
% 14.93/3.05  
% 14.93/3.05  fof(f18,axiom,(
% 14.93/3.05    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f47,plain,(
% 14.93/3.05    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f18])).
% 14.93/3.05  
% 14.93/3.05  fof(f19,axiom,(
% 14.93/3.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f48,plain,(
% 14.93/3.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f19])).
% 14.93/3.05  
% 14.93/3.05  fof(f57,plain,(
% 14.93/3.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 14.93/3.05    inference(definition_unfolding,[],[f47,f48])).
% 14.93/3.05  
% 14.93/3.05  fof(f58,plain,(
% 14.93/3.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 14.93/3.05    inference(definition_unfolding,[],[f46,f57])).
% 14.93/3.05  
% 14.93/3.05  fof(f66,plain,(
% 14.93/3.05    ( ! [X2,X0,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 14.93/3.05    inference(definition_unfolding,[],[f41,f32,f57,f59,f58])).
% 14.93/3.05  
% 14.93/3.05  fof(f23,conjecture,(
% 14.93/3.05    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f24,negated_conjecture,(
% 14.93/3.05    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 14.93/3.05    inference(negated_conjecture,[],[f23])).
% 14.93/3.05  
% 14.93/3.05  fof(f29,plain,(
% 14.93/3.05    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 14.93/3.05    inference(ennf_transformation,[],[f24])).
% 14.93/3.05  
% 14.93/3.05  fof(f30,plain,(
% 14.93/3.05    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)))),
% 14.93/3.05    introduced(choice_axiom,[])).
% 14.93/3.05  
% 14.93/3.05  fof(f31,plain,(
% 14.93/3.05    sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 14.93/3.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 14.93/3.05  
% 14.93/3.05  fof(f54,plain,(
% 14.93/3.05    sK0 != sK2),
% 14.93/3.05    inference(cnf_transformation,[],[f31])).
% 14.93/3.05  
% 14.93/3.05  fof(f13,axiom,(
% 14.93/3.05    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f42,plain,(
% 14.93/3.05    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f13])).
% 14.93/3.05  
% 14.93/3.05  fof(f7,axiom,(
% 14.93/3.05    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f36,plain,(
% 14.93/3.05    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f7])).
% 14.93/3.05  
% 14.93/3.05  fof(f55,plain,(
% 14.93/3.05    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 14.93/3.05    inference(definition_unfolding,[],[f36,f32])).
% 14.93/3.05  
% 14.93/3.05  fof(f63,plain,(
% 14.93/3.05    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 14.93/3.05    inference(definition_unfolding,[],[f42,f55,f48,f59])).
% 14.93/3.05  
% 14.93/3.05  fof(f6,axiom,(
% 14.93/3.05    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f35,plain,(
% 14.93/3.05    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 14.93/3.05    inference(cnf_transformation,[],[f6])).
% 14.93/3.05  
% 14.93/3.05  fof(f14,axiom,(
% 14.93/3.05    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f43,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f14])).
% 14.93/3.05  
% 14.93/3.05  fof(f22,axiom,(
% 14.93/3.05    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f51,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f22])).
% 14.93/3.05  
% 14.93/3.05  fof(f61,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 14.93/3.05    inference(definition_unfolding,[],[f51,f56])).
% 14.93/3.05  
% 14.93/3.05  fof(f8,axiom,(
% 14.93/3.05    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f37,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f8])).
% 14.93/3.05  
% 14.93/3.05  fof(f56,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.93/3.05    inference(definition_unfolding,[],[f37,f55,f48,f48])).
% 14.93/3.05  
% 14.93/3.05  fof(f67,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 14.93/3.05    inference(definition_unfolding,[],[f43,f55,f59,f61,f56])).
% 14.93/3.05  
% 14.93/3.05  fof(f15,axiom,(
% 14.93/3.05    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f44,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f15])).
% 14.93/3.05  
% 14.93/3.05  fof(f68,plain,(
% 14.93/3.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))))))) )),
% 14.93/3.05    inference(definition_unfolding,[],[f44,f55,f61,f59,f56])).
% 14.93/3.05  
% 14.93/3.05  fof(f4,axiom,(
% 14.93/3.05    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f34,plain,(
% 14.93/3.05    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 14.93/3.05    inference(cnf_transformation,[],[f4])).
% 14.93/3.05  
% 14.93/3.05  fof(f52,plain,(
% 14.93/3.05    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 14.93/3.05    inference(cnf_transformation,[],[f31])).
% 14.93/3.05  
% 14.93/3.05  fof(f70,plain,(
% 14.93/3.05    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 14.93/3.05    inference(definition_unfolding,[],[f52,f59,f58])).
% 14.93/3.05  
% 14.93/3.05  fof(f3,axiom,(
% 14.93/3.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 14.93/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/3.05  
% 14.93/3.05  fof(f27,plain,(
% 14.93/3.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 14.93/3.05    inference(ennf_transformation,[],[f3])).
% 14.93/3.05  
% 14.93/3.05  fof(f33,plain,(
% 14.93/3.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 14.93/3.05    inference(cnf_transformation,[],[f27])).
% 14.93/3.05  
% 14.93/3.05  fof(f53,plain,(
% 14.93/3.05    sK0 != sK1),
% 14.93/3.05    inference(cnf_transformation,[],[f31])).
% 14.93/3.05  
% 14.93/3.05  cnf(c_35,plain,( X0_2 = X0_2 ),theory(equality) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_6,plain,
% 14.93/3.05      ( X0 = X1
% 14.93/3.05      | X2 = X1
% 14.93/3.05      | k5_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X2) ),
% 14.93/3.05      inference(cnf_transformation,[],[f66]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3033,plain,
% 14.93/3.05      ( ~ iProver_ARSWP_43
% 14.93/3.05      | X0 = X1
% 14.93/3.05      | X2 = X1
% 14.93/3.05      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0 ),
% 14.93/3.05      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3138,plain,
% 14.93/3.05      ( X0 = X1
% 14.93/3.05      | X2 = X1
% 14.93/3.05      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(predicate_to_equality,[status(thm)],[c_3033]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10,negated_conjecture,
% 14.93/3.05      ( sK0 != sK2 ),
% 14.93/3.05      inference(cnf_transformation,[],[f54]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3290,plain,
% 14.93/3.05      ( ~ iProver_ARSWP_43
% 14.93/3.05      | X0 = sK2
% 14.93/3.05      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | sK0 = sK2 ),
% 14.93/3.05      inference(instantiation,[status(thm)],[c_3033]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3291,plain,
% 14.93/3.05      ( X0 = sK2
% 14.93/3.05      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | sK0 = sK2
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(predicate_to_equality,[status(thm)],[c_3290]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3293,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | sK0 = sK2
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(instantiation,[status(thm)],[c_3291]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3555,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(global_propositional_subsumption,
% 14.93/3.05                [status(thm)],
% 14.93/3.05                [c_3138,c_10,c_3293]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_0,plain,
% 14.93/3.05      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 14.93/3.05      inference(cnf_transformation,[],[f63]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3030,plain,
% 14.93/3.05      ( ~ iProver_ARSWP_40
% 14.93/3.05      | k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0 ),
% 14.93/3.05      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3141,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(predicate_to_equality,[status(thm)],[c_3030]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3565,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_3141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3,plain,
% 14.93/3.05      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 14.93/3.05      inference(cnf_transformation,[],[f35]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3569,plain,
% 14.93/3.05      ( arAF0_k3_enumset1_0 = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_3565,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3607,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_3555]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7,plain,
% 14.93/3.05      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X1,X1,X1,X2,X3)))),k3_enumset1(X0,X0,X0,X0,X0)))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
% 14.93/3.05      inference(cnf_transformation,[],[f67]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3034,plain,
% 14.93/3.05      ( ~ iProver_ARSWP_44
% 14.93/3.05      | k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) ),
% 14.93/3.05      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3137,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top ),
% 14.93/3.05      inference(predicate_to_equality,[status(thm)],[c_3034]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4136,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4168,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_4136,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4543,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4545,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4168,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_14559,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4543,c_4545]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_26050,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3607,c_14559]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3618,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_3141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2))))))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
% 14.93/3.05      inference(cnf_transformation,[],[f68]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3035,plain,
% 14.93/3.05      ( ~ iProver_ARSWP_45
% 14.93/3.05      | k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) ),
% 14.93/3.05      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3136,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top ),
% 14.93/3.05      inference(predicate_to_equality,[status(thm)],[c_3035]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3612,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_6533,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3618,c_3612]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3563,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3576,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_3563,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4299,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4364,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_4299,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4308,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3576,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7340,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4364,c_4308]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19429,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6533,c_7340]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19440,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6533,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_25339,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_19440]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_25513,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_19429,c_25339]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11467,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4548,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4168,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_14925,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_4548]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_24793,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_11467,c_14925]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4141,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11391,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3618,c_4141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23175,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_11391]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_24271,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_23175]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7343,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_4308]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18835,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_22898,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_18835]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23670,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_22898]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_2,plain,
% 14.93/3.05      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 14.93/3.05      inference(cnf_transformation,[],[f34]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23675,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_23670,c_2]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23170,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_11391]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23255,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_23170,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23188,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_11391,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23192,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_11391,c_3141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_23186,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_11391,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_12,negated_conjecture,
% 14.93/3.05      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
% 14.93/3.05      inference(cnf_transformation,[],[f70]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3036,negated_conjecture,
% 14.93/3.05      ( arAF0_r1_tarski_0_1(arAF0_k3_enumset1_0) | ~ iProver_ARSWP_46 ),
% 14.93/3.05      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3135,plain,
% 14.93/3.05      ( arAF0_r1_tarski_0_1(arAF0_k3_enumset1_0) = iProver_top
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top ),
% 14.93/3.05      inference(predicate_to_equality,[status(thm)],[c_3036]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_1,plain,
% 14.93/3.05      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 14.93/3.05      inference(cnf_transformation,[],[f33]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3031,plain,
% 14.93/3.05      ( ~ arAF0_r1_tarski_0_1(X0)
% 14.93/3.05      | ~ iProver_ARSWP_41
% 14.93/3.05      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 14.93/3.05      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3140,plain,
% 14.93/3.05      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 14.93/3.05      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(predicate_to_equality,[status(thm)],[c_3031]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3403,plain,
% 14.93/3.05      ( arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3135,c_3140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3561,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3403,c_3555]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3595,plain,
% 14.93/3.05      ( arAF0_k3_enumset1_0 = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_3561,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3479,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3403,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3481,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_3479,c_2,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3725,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_3481]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3728,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8715,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3725,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15979,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_7340]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15990,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_21791,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_15990]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_22078,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_15979,c_21791]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7348,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_4308]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7353,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_7348,c_2]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18829,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_7353]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_20958,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_18829,c_3612]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_20950,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_18829,c_4141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3733,plain,
% 14.93/3.05      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_3403]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7347,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_4308]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7363,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_7347,c_2]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18827,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_7363]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_20095,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_18827,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_20206,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_20095]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3723,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_3555]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_20204,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3723,c_20095]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4140,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_20093,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_18827,c_4140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19421,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_6533]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19506,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_19421,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19441,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6533,c_3141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19436,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6533,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19435,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6533,c_7353]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_19427,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6533,c_7343]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18815,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_7343]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18956,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_18815,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18832,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18836,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_3141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18834,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_3481]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18831,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18830,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_5077,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_3725]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8723,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_9884,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_5077,c_8723]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18826,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_9884]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3737,plain,
% 14.93/3.05      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_3135]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3924,plain,
% 14.93/3.05      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3737,c_3140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8722,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3924,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8739,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_8722,c_2]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_9154,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_8739]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10169,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_9154]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10221,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_10169,c_8723]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18825,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_10221]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18823,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_7340]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18822,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7343,c_8715]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10617,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_9884,c_7363]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_14631,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_10617,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18478,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_14631]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_9514,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7363,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18418,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_9514]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10958,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_10221,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18259,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_10958]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10625,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_9884,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_18162,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_10625]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4541,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3403,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4615,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_4541,c_2,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4894,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_4615]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8829,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4894,c_4140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17162,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8829,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17844,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_17162]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8836,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3924,c_4140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8853,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_8836,c_2]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17156,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8829,c_8853]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17346,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_17156]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17149,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_8829]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17246,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_17149,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17152,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3403,c_8829]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17235,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_17152,c_2,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_17164,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8829,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7409,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7353,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_16933,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_7409]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15989,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_3481]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15986,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15984,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_8739]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15983,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_7363]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15982,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_9884]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15981,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8715,c_10221]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4542,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_6268,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4542]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_6317,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_6268]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_14568,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4545]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15222,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6317,c_14568]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_6315,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3723,c_6268]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_15221,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6315,c_14568]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10950,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_10221,c_7363]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_14863,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_10950,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8709,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6268,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_12514,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_8709]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_12502,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6317,c_8709]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11455,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_7340]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11577,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_11455,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11472,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_3136]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11469,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11473,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_3141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11471,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_3481]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11468,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11466,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_7353]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11464,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_7363]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11463,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_9884]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11462,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_7340,c_10221]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11394,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3607,c_4141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4538,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_4168]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4624,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_4538,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4641,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_4624]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11390,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4641,c_4141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11063,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_8853,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10949,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_10221,c_9884]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10624,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_9884,c_3481]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10621,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_9884,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_10618,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_9884,c_8739]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8837,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8835,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3723,c_4140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8827,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6268,c_4140]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4303,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_8710,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4303,c_3728]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7647,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_6315,c_6317]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7401,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3555,c_7353]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_7454,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(demodulation,[status(thm)],[c_7401,c_3]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4304,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_6956,plain,
% 14.93/3.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4304,c_3612]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_6049,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4303]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_5892,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4894]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_5706,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3607,c_4641]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_5540,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_3618]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_5537,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3607,c_3618]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4640,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3595,c_4624]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_5266,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4640]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_5264,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3723,c_4640]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4898,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4615]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4644,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_4624]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4549,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4168,c_3141]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4544,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_4168,c_3576]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4305,plain,
% 14.93/3.05      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)))) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k3_enumset1_0)))
% 14.93/3.05      | iProver_ARSWP_45 != iProver_top
% 14.93/3.05      | iProver_ARSWP_44 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3576,c_3137]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_4023,plain,
% 14.93/3.05      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_41 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3733,c_3723]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_3621,plain,
% 14.93/3.05      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 14.93/3.05      | iProver_ARSWP_46 != iProver_top
% 14.93/3.05      | iProver_ARSWP_43 != iProver_top
% 14.93/3.05      | iProver_ARSWP_40 != iProver_top ),
% 14.93/3.05      inference(superposition,[status(thm)],[c_3569,c_3135]) ).
% 14.93/3.05  
% 14.93/3.05  cnf(c_11,negated_conjecture,
% 14.93/3.05      ( sK0 != sK1 ),
% 14.93/3.05      inference(cnf_transformation,[],[f53]) ).
% 14.93/3.05  
% 14.93/3.05  
% 14.93/3.05  % SZS output end Saturation for theBenchmark.p
% 14.93/3.05  
% 14.93/3.05  ------                               Statistics
% 14.93/3.05  
% 14.93/3.05  ------ Selected
% 14.93/3.05  
% 14.93/3.05  total_time:                             2.198
% 14.93/3.05  
%------------------------------------------------------------------------------
