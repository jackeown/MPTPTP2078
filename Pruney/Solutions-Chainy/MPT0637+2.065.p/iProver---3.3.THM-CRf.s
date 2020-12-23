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
% DateTime   : Thu Dec  3 11:50:06 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  150 (6278 expanded)
%              Number of clauses        :   89 (2602 expanded)
%              Number of leaves         :   20 (1374 expanded)
%              Depth                    :   31
%              Number of atoms          :  227 (9486 expanded)
%              Number of equality atoms :  165 (5498 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f35,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).

fof(f58,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f58,f64])).

cnf(c_2,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_407,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_400,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_970,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_407,c_400])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_971,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_970,c_8])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_409,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1073,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_971,c_409])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_402,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1889,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_402])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_399,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_649,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_407,c_399])).

cnf(c_1893,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1889,c_649])).

cnf(c_42,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5231,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1893,c_42])).

cnf(c_5232,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5231])).

cnf(c_5238,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_1073,c_5232])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_408,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1623,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_408])).

cnf(c_3588,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1623,c_42])).

cnf(c_3594,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3588,c_407])).

cnf(c_1074,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_971,c_400])).

cnf(c_3605,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_3594,c_1074])).

cnf(c_6891,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(superposition,[status(thm)],[c_5238,c_3605])).

cnf(c_1887,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_402])).

cnf(c_5214,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1887,c_3594])).

cnf(c_3600,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_3594,c_399])).

cnf(c_5222,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_5214,c_3600])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_404,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1994,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_404])).

cnf(c_9,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1997,plain,
    ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1994,c_9])).

cnf(c_3602,plain,
    ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_3594,c_1997])).

cnf(c_2783,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_407,c_1997])).

cnf(c_2785,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_2783,c_9,c_649])).

cnf(c_2786,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_2785,c_649])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_406,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3197,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_406])).

cnf(c_3359,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_407,c_3197])).

cnf(c_3361,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3359,c_649])).

cnf(c_3619,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_3602,c_2786,c_3361])).

cnf(c_3626,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(demodulation,[status(thm)],[c_3600,c_3619])).

cnf(c_5321,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_5222,c_3626])).

cnf(c_5323,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_5321,c_5222])).

cnf(c_5341,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_5323,c_2786])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_401,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_574,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_407,c_401])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_575,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_574,c_7])).

cnf(c_1624,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_649,c_575])).

cnf(c_3374,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1624,c_3361])).

cnf(c_3393,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_3374,c_649])).

cnf(c_5397,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_5341,c_3393])).

cnf(c_6896,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_6891,c_5397])).

cnf(c_7018,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_6896,c_8])).

cnf(c_1747,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1073])).

cnf(c_1748,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1747,c_8])).

cnf(c_1888,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_402])).

cnf(c_3604,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3594,c_1888])).

cnf(c_4972,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3604,c_3600])).

cnf(c_7069,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_7018,c_4972])).

cnf(c_8675,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_7069,c_3626])).

cnf(c_8681,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_8675,c_5238])).

cnf(c_8682,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_8681,c_5323])).

cnf(c_8978,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_8682,c_5341])).

cnf(c_9244,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_5238,c_8978])).

cnf(c_3606,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3594,c_401])).

cnf(c_4585,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3606,c_3361])).

cnf(c_4944,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_4585,c_3626])).

cnf(c_4950,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_4944,c_2786])).

cnf(c_6885,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_5238,c_4950])).

cnf(c_5382,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_5341,c_5222])).

cnf(c_6911,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
    inference(demodulation,[status(thm)],[c_6885,c_7,c_5382])).

cnf(c_6912,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_6911,c_5238])).

cnf(c_9399,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_9244,c_6896,c_6912,c_8978])).

cnf(c_14,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1075,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_971,c_14])).

cnf(c_1621,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_649,c_1075])).

cnf(c_5346,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_5341,c_1621])).

cnf(c_9582,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_9399,c_5346])).

cnf(c_9583,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9582])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.84/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.00  
% 3.84/1.00  ------  iProver source info
% 3.84/1.00  
% 3.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.00  git: non_committed_changes: false
% 3.84/1.00  git: last_make_outside_of_git: false
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    --mode clausify
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             all
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         305.
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              default
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           true
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             true
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         false
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     num_symb
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       true
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     false
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   []
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_full_bw                           [BwDemod]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  ------ Parsing...
% 3.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  ------ Proving...
% 3.84/1.00  ------ Problem Properties 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  clauses                                 15
% 3.84/1.00  conjectures                             1
% 3.84/1.00  EPR                                     0
% 3.84/1.00  Horn                                    15
% 3.84/1.00  unary                                   6
% 3.84/1.00  binary                                  3
% 3.84/1.00  lits                                    31
% 3.84/1.00  lits eq                                 11
% 3.84/1.00  fd_pure                                 0
% 3.84/1.00  fd_pseudo                               0
% 3.84/1.00  fd_cond                                 0
% 3.84/1.00  fd_pseudo_cond                          0
% 3.84/1.00  AC symbols                              0
% 3.84/1.00  
% 3.84/1.00  ------ Schedule dynamic 5 is on 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  Current options:
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    --mode clausify
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             all
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         305.
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              default
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           true
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             true
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         false
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     none
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       false
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     false
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   []
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_full_bw                           [BwDemod]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS status Theorem for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00   Resolution empty clause
% 3.84/1.00  
% 3.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  fof(f10,axiom,(
% 3.84/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f46,plain,(
% 3.84/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.84/1.00    inference(cnf_transformation,[],[f10])).
% 3.84/1.00  
% 3.84/1.00  fof(f19,axiom,(
% 3.84/1.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f32,plain,(
% 3.84/1.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.84/1.00    inference(ennf_transformation,[],[f19])).
% 3.84/1.00  
% 3.84/1.00  fof(f56,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f32])).
% 3.84/1.00  
% 3.84/1.00  fof(f8,axiom,(
% 3.84/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f44,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.84/1.00    inference(cnf_transformation,[],[f8])).
% 3.84/1.00  
% 3.84/1.00  fof(f2,axiom,(
% 3.84/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f38,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f2])).
% 3.84/1.00  
% 3.84/1.00  fof(f3,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f39,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f3])).
% 3.84/1.00  
% 3.84/1.00  fof(f4,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f40,plain,(
% 3.84/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f4])).
% 3.84/1.00  
% 3.84/1.00  fof(f5,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f41,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f5])).
% 3.84/1.00  
% 3.84/1.00  fof(f6,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f42,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f6])).
% 3.84/1.00  
% 3.84/1.00  fof(f7,axiom,(
% 3.84/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f43,plain,(
% 3.84/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f7])).
% 3.84/1.00  
% 3.84/1.00  fof(f59,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f42,f43])).
% 3.84/1.00  
% 3.84/1.00  fof(f60,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f41,f59])).
% 3.84/1.00  
% 3.84/1.00  fof(f61,plain,(
% 3.84/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f40,f60])).
% 3.84/1.00  
% 3.84/1.00  fof(f62,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f39,f61])).
% 3.84/1.00  
% 3.84/1.00  fof(f63,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f38,f62])).
% 3.84/1.00  
% 3.84/1.00  fof(f64,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.84/1.00    inference(definition_unfolding,[],[f44,f63])).
% 3.84/1.00  
% 3.84/1.00  fof(f66,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f56,f64])).
% 3.84/1.00  
% 3.84/1.00  fof(f15,axiom,(
% 3.84/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f51,plain,(
% 3.84/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.84/1.00    inference(cnf_transformation,[],[f15])).
% 3.84/1.00  
% 3.84/1.00  fof(f1,axiom,(
% 3.84/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f37,plain,(
% 3.84/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f1])).
% 3.84/1.00  
% 3.84/1.00  fof(f65,plain,(
% 3.84/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.84/1.00    inference(definition_unfolding,[],[f37,f64])).
% 3.84/1.00  
% 3.84/1.00  fof(f17,axiom,(
% 3.84/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f29,plain,(
% 3.84/1.00    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.84/1.00    inference(ennf_transformation,[],[f17])).
% 3.84/1.00  
% 3.84/1.00  fof(f30,plain,(
% 3.84/1.00    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.84/1.00    inference(flattening,[],[f29])).
% 3.84/1.00  
% 3.84/1.00  fof(f54,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f30])).
% 3.84/1.00  
% 3.84/1.00  fof(f20,axiom,(
% 3.84/1.00    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f33,plain,(
% 3.84/1.00    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.84/1.00    inference(ennf_transformation,[],[f20])).
% 3.84/1.00  
% 3.84/1.00  fof(f57,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f33])).
% 3.84/1.00  
% 3.84/1.00  fof(f9,axiom,(
% 3.84/1.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f23,plain,(
% 3.84/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f9])).
% 3.84/1.00  
% 3.84/1.00  fof(f24,plain,(
% 3.84/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.84/1.00    inference(flattening,[],[f23])).
% 3.84/1.00  
% 3.84/1.00  fof(f45,plain,(
% 3.84/1.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f13,axiom,(
% 3.84/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f27,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f13])).
% 3.84/1.00  
% 3.84/1.00  fof(f49,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f27])).
% 3.84/1.00  
% 3.84/1.00  fof(f16,axiom,(
% 3.84/1.00    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f53,plain,(
% 3.84/1.00    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 3.84/1.00    inference(cnf_transformation,[],[f16])).
% 3.84/1.00  
% 3.84/1.00  fof(f11,axiom,(
% 3.84/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f25,plain,(
% 3.84/1.00    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.84/1.00    inference(ennf_transformation,[],[f11])).
% 3.84/1.00  
% 3.84/1.00  fof(f47,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f25])).
% 3.84/1.00  
% 3.84/1.00  fof(f18,axiom,(
% 3.84/1.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f31,plain,(
% 3.84/1.00    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f18])).
% 3.84/1.00  
% 3.84/1.00  fof(f55,plain,(
% 3.84/1.00    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f31])).
% 3.84/1.00  
% 3.84/1.00  fof(f52,plain,(
% 3.84/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.84/1.00    inference(cnf_transformation,[],[f15])).
% 3.84/1.00  
% 3.84/1.00  fof(f21,conjecture,(
% 3.84/1.00    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f22,negated_conjecture,(
% 3.84/1.00    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.84/1.00    inference(negated_conjecture,[],[f21])).
% 3.84/1.00  
% 3.84/1.00  fof(f34,plain,(
% 3.84/1.00    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.84/1.00    inference(ennf_transformation,[],[f22])).
% 3.84/1.00  
% 3.84/1.00  fof(f35,plain,(
% 3.84/1.00    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f36,plain,(
% 3.84/1.00    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).
% 3.84/1.00  
% 3.84/1.00  fof(f58,plain,(
% 3.84/1.00    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.84/1.00    inference(cnf_transformation,[],[f36])).
% 3.84/1.00  
% 3.84/1.00  fof(f67,plain,(
% 3.84/1.00    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 3.84/1.00    inference(definition_unfolding,[],[f58,f64])).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2,plain,
% 3.84/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_407,plain,
% 3.84/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12,plain,
% 3.84/1.00      ( ~ v1_relat_1(X0)
% 3.84/1.00      | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_400,plain,
% 3.84/1.00      ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_970,plain,
% 3.84/1.00      ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_407,c_400]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8,plain,
% 3.84/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_971,plain,
% 3.84/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_970,c_8]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_0,plain,
% 3.84/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_409,plain,
% 3.84/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1073,plain,
% 3.84/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_971,c_409]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10,plain,
% 3.84/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.84/1.00      | ~ v1_relat_1(X0)
% 3.84/1.00      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_402,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 3.84/1.00      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.84/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1889,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 3.84/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.84/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_8,c_402]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13,plain,
% 3.84/1.00      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_399,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.84/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_649,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_407,c_399]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1893,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.84/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.84/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_1889,c_649]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_42,plain,
% 3.84/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5231,plain,
% 3.84/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.84/1.00      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1893,c_42]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5232,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.84/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_5231]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5238,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1073,c_5232]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1,plain,
% 3.84/1.00      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_408,plain,
% 3.84/1.00      ( v1_relat_1(X0) != iProver_top
% 3.84/1.00      | v1_relat_1(X1) != iProver_top
% 3.84/1.00      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1623,plain,
% 3.84/1.00      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.84/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 3.84/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_649,c_408]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3588,plain,
% 3.84/1.00      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.84/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1623,c_42]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3594,plain,
% 3.84/1.00      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 3.84/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3588,c_407]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1074,plain,
% 3.84/1.00      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_971,c_400]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3605,plain,
% 3.84/1.00      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3594,c_1074]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6891,plain,
% 3.84/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5238,c_3605]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1887,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 3.84/1.00      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1073,c_402]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5214,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1887,c_3594]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3600,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3594,c_399]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5222,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5214,c_3600]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5,plain,
% 3.84/1.00      ( ~ v1_relat_1(X0)
% 3.84/1.00      | ~ v1_relat_1(X1)
% 3.84/1.00      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_404,plain,
% 3.84/1.00      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 3.84/1.00      | v1_relat_1(X0) != iProver_top
% 3.84/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1994,plain,
% 3.84/1.00      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 3.84/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_407,c_404]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9,plain,
% 3.84/1.00      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1997,plain,
% 3.84/1.00      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
% 3.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_1994,c_9]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3602,plain,
% 3.84/1.00      ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3594,c_1997]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2783,plain,
% 3.84/1.00      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_407,c_1997]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2785,plain,
% 3.84/1.00      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_2783,c_9,c_649]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2786,plain,
% 3.84/1.00      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_2785,c_649]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3,plain,
% 3.84/1.00      ( ~ v1_relat_1(X0)
% 3.84/1.00      | ~ v1_relat_1(X1)
% 3.84/1.00      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_406,plain,
% 3.84/1.00      ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
% 3.84/1.00      | v1_relat_1(X0) != iProver_top
% 3.84/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3197,plain,
% 3.84/1.00      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 3.84/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_407,c_406]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3359,plain,
% 3.84/1.00      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_407,c_3197]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3361,plain,
% 3.84/1.00      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_3359,c_649]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3619,plain,
% 3.84/1.00      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_3602,c_2786,c_3361]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3626,plain,
% 3.84/1.00      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_3600,c_3619]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5321,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5222,c_3626]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5323,plain,
% 3.84/1.00      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_5321,c_5222]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5341,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5323,c_2786]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11,plain,
% 3.84/1.00      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_401,plain,
% 3.84/1.00      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_574,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_407,c_401]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7,plain,
% 3.84/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_575,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_574,c_7]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1624,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_649,c_575]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3374,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1624,c_3361]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3393,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_3374,c_649]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5397,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5341,c_3393]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6896,plain,
% 3.84/1.00      ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_6891,c_5397]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7018,plain,
% 3.84/1.00      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_6896,c_8]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1747,plain,
% 3.84/1.00      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1624,c_1073]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1748,plain,
% 3.84/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_1747,c_8]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1888,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 3.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1748,c_402]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3604,plain,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3594,c_1888]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4972,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3604,c_3600]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7069,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7018,c_4972]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8675,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7069,c_3626]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8681,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_8675,c_5238]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8682,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_8681,c_5323]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8978,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_8682,c_5341]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9244,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5238,c_8978]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3606,plain,
% 3.84/1.00      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3594,c_401]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4585,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3606,c_3361]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4944,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4585,c_3626]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4950,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_4944,c_2786]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6885,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5238,c_4950]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5382,plain,
% 3.84/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5341,c_5222]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6911,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_6885,c_7,c_5382]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6912,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_6911,c_5238]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9399,plain,
% 3.84/1.00      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.84/1.00      inference(light_normalisation,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_9244,c_6896,c_6912,c_8978]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_14,negated_conjecture,
% 3.84/1.00      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 3.84/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1075,plain,
% 3.84/1.00      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_971,c_14]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1621,plain,
% 3.84/1.00      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_649,c_1075]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5346,plain,
% 3.84/1.00      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_5341,c_1621]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9582,plain,
% 3.84/1.00      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_9399,c_5346]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9583,plain,
% 3.84/1.00      ( $false ),
% 3.84/1.00      inference(equality_resolution_simp,[status(thm)],[c_9582]) ).
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  ------                               Statistics
% 3.84/1.00  
% 3.84/1.00  ------ General
% 3.84/1.00  
% 3.84/1.00  abstr_ref_over_cycles:                  0
% 3.84/1.00  abstr_ref_under_cycles:                 0
% 3.84/1.00  gc_basic_clause_elim:                   0
% 3.84/1.00  forced_gc_time:                         0
% 3.84/1.00  parsing_time:                           0.008
% 3.84/1.00  unif_index_cands_time:                  0.
% 3.84/1.00  unif_index_add_time:                    0.
% 3.84/1.00  orderings_time:                         0.
% 3.84/1.00  out_proof_time:                         0.009
% 3.84/1.00  total_time:                             0.309
% 3.84/1.00  num_of_symbols:                         43
% 3.84/1.00  num_of_terms:                           14656
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing
% 3.84/1.00  
% 3.84/1.00  num_of_splits:                          0
% 3.84/1.00  num_of_split_atoms:                     0
% 3.84/1.00  num_of_reused_defs:                     0
% 3.84/1.00  num_eq_ax_congr_red:                    2
% 3.84/1.00  num_of_sem_filtered_clauses:            1
% 3.84/1.00  num_of_subtypes:                        0
% 3.84/1.00  monotx_restored_types:                  0
% 3.84/1.00  sat_num_of_epr_types:                   0
% 3.84/1.00  sat_num_of_non_cyclic_types:            0
% 3.84/1.00  sat_guarded_non_collapsed_types:        0
% 3.84/1.00  num_pure_diseq_elim:                    0
% 3.84/1.00  simp_replaced_by:                       0
% 3.84/1.00  res_preprocessed:                       70
% 3.84/1.00  prep_upred:                             0
% 3.84/1.00  prep_unflattend:                        2
% 3.84/1.00  smt_new_axioms:                         0
% 3.84/1.00  pred_elim_cands:                        2
% 3.84/1.00  pred_elim:                              0
% 3.84/1.00  pred_elim_cl:                           0
% 3.84/1.00  pred_elim_cycles:                       1
% 3.84/1.00  merged_defs:                            0
% 3.84/1.00  merged_defs_ncl:                        0
% 3.84/1.00  bin_hyper_res:                          0
% 3.84/1.00  prep_cycles:                            3
% 3.84/1.00  pred_elim_time:                         0.001
% 3.84/1.00  splitting_time:                         0.016
% 3.84/1.00  sem_filter_time:                        0.
% 3.84/1.00  monotx_time:                            0.
% 3.84/1.00  subtype_inf_time:                       0.
% 3.84/1.00  
% 3.84/1.00  ------ Problem properties
% 3.84/1.00  
% 3.84/1.00  clauses:                                15
% 3.84/1.00  conjectures:                            1
% 3.84/1.00  epr:                                    0
% 3.84/1.00  horn:                                   15
% 3.84/1.00  ground:                                 1
% 3.84/1.00  unary:                                  6
% 3.84/1.00  binary:                                 3
% 3.84/1.00  lits:                                   31
% 3.84/1.00  lits_eq:                                11
% 3.84/1.00  fd_pure:                                0
% 3.84/1.00  fd_pseudo:                              0
% 3.84/1.00  fd_cond:                                0
% 3.84/1.00  fd_pseudo_cond:                         0
% 3.84/1.00  ac_symbols:                             0
% 3.84/1.00  
% 3.84/1.00  ------ Propositional Solver
% 3.84/1.00  
% 3.84/1.00  prop_solver_calls:                      26
% 3.84/1.00  prop_fast_solver_calls:                 530
% 3.84/1.00  smt_solver_calls:                       0
% 3.84/1.00  smt_fast_solver_calls:                  0
% 3.84/1.00  prop_num_of_clauses:                    3915
% 3.84/1.00  prop_preprocess_simplified:             7013
% 3.84/1.00  prop_fo_subsumed:                       4
% 3.84/1.00  prop_solver_time:                       0.
% 3.84/1.00  smt_solver_time:                        0.
% 3.84/1.00  smt_fast_solver_time:                   0.
% 3.84/1.00  prop_fast_solver_time:                  0.
% 3.84/1.00  prop_unsat_core_time:                   0.
% 3.84/1.00  
% 3.84/1.00  ------ QBF
% 3.84/1.00  
% 3.84/1.00  qbf_q_res:                              0
% 3.84/1.00  qbf_num_tautologies:                    0
% 3.84/1.00  qbf_prep_cycles:                        0
% 3.84/1.00  
% 3.84/1.00  ------ BMC1
% 3.84/1.00  
% 3.84/1.00  bmc1_current_bound:                     -1
% 3.84/1.00  bmc1_last_solved_bound:                 -1
% 3.84/1.00  bmc1_unsat_core_size:                   -1
% 3.84/1.00  bmc1_unsat_core_parents_size:           -1
% 3.84/1.00  bmc1_merge_next_fun:                    0
% 3.84/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation
% 3.84/1.00  
% 3.84/1.00  inst_num_of_clauses:                    1094
% 3.84/1.00  inst_num_in_passive:                    405
% 3.84/1.00  inst_num_in_active:                     565
% 3.84/1.00  inst_num_in_unprocessed:                124
% 3.84/1.00  inst_num_of_loops:                      600
% 3.84/1.00  inst_num_of_learning_restarts:          0
% 3.84/1.00  inst_num_moves_active_passive:          33
% 3.84/1.00  inst_lit_activity:                      0
% 3.84/1.00  inst_lit_activity_moves:                1
% 3.84/1.00  inst_num_tautologies:                   0
% 3.84/1.00  inst_num_prop_implied:                  0
% 3.84/1.00  inst_num_existing_simplified:           0
% 3.84/1.00  inst_num_eq_res_simplified:             0
% 3.84/1.00  inst_num_child_elim:                    0
% 3.84/1.00  inst_num_of_dismatching_blockings:      319
% 3.84/1.00  inst_num_of_non_proper_insts:           591
% 3.84/1.00  inst_num_of_duplicates:                 0
% 3.84/1.00  inst_inst_num_from_inst_to_res:         0
% 3.84/1.00  inst_dismatching_checking_time:         0.
% 3.84/1.00  
% 3.84/1.00  ------ Resolution
% 3.84/1.00  
% 3.84/1.00  res_num_of_clauses:                     0
% 3.84/1.00  res_num_in_passive:                     0
% 3.84/1.00  res_num_in_active:                      0
% 3.84/1.00  res_num_of_loops:                       73
% 3.84/1.00  res_forward_subset_subsumed:            64
% 3.84/1.00  res_backward_subset_subsumed:           2
% 3.84/1.00  res_forward_subsumed:                   0
% 3.84/1.00  res_backward_subsumed:                  0
% 3.84/1.00  res_forward_subsumption_resolution:     0
% 3.84/1.00  res_backward_subsumption_resolution:    0
% 3.84/1.00  res_clause_to_clause_subsumption:       1928
% 3.84/1.00  res_orphan_elimination:                 0
% 3.84/1.00  res_tautology_del:                      77
% 3.84/1.00  res_num_eq_res_simplified:              0
% 3.84/1.00  res_num_sel_changes:                    0
% 3.84/1.00  res_moves_from_active_to_pass:          0
% 3.84/1.00  
% 3.84/1.00  ------ Superposition
% 3.84/1.00  
% 3.84/1.00  sup_time_total:                         0.
% 3.84/1.00  sup_time_generating:                    0.
% 3.84/1.00  sup_time_sim_full:                      0.
% 3.84/1.00  sup_time_sim_immed:                     0.
% 3.84/1.00  
% 3.84/1.00  sup_num_of_clauses:                     336
% 3.84/1.00  sup_num_in_active:                      102
% 3.84/1.00  sup_num_in_passive:                     234
% 3.84/1.00  sup_num_of_loops:                       118
% 3.84/1.00  sup_fw_superposition:                   723
% 3.84/1.00  sup_bw_superposition:                   829
% 3.84/1.00  sup_immediate_simplified:               535
% 3.84/1.00  sup_given_eliminated:                   0
% 3.84/1.00  comparisons_done:                       0
% 3.84/1.00  comparisons_avoided:                    0
% 3.84/1.00  
% 3.84/1.00  ------ Simplifications
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  sim_fw_subset_subsumed:                 16
% 3.84/1.00  sim_bw_subset_subsumed:                 4
% 3.84/1.00  sim_fw_subsumed:                        86
% 3.84/1.00  sim_bw_subsumed:                        0
% 3.84/1.00  sim_fw_subsumption_res:                 5
% 3.84/1.00  sim_bw_subsumption_res:                 0
% 3.84/1.00  sim_tautology_del:                      5
% 3.84/1.00  sim_eq_tautology_del:                   70
% 3.84/1.00  sim_eq_res_simp:                        0
% 3.84/1.00  sim_fw_demodulated:                     167
% 3.84/1.00  sim_bw_demodulated:                     24
% 3.84/1.00  sim_light_normalised:                   317
% 3.84/1.00  sim_joinable_taut:                      0
% 3.84/1.00  sim_joinable_simp:                      0
% 3.84/1.00  sim_ac_normalised:                      0
% 3.84/1.00  sim_smt_subsumption:                    0
% 3.84/1.00  
%------------------------------------------------------------------------------
