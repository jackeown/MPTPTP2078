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
% DateTime   : Thu Dec  3 11:50:05 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 750 expanded)
%              Number of clauses        :   72 ( 376 expanded)
%              Number of leaves         :   22 ( 144 expanded)
%              Depth                    :   18
%              Number of atoms          :  264 (1258 expanded)
%              Number of equality atoms :  161 ( 660 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f79,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f24,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f24])).

fof(f44,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f25])).

fof(f45,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f45])).

fof(f73,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f73,f79])).

cnf(c_1,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_530,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_515,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_813,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_530,c_515])).

cnf(c_13,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_520,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_956,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_520])).

cnf(c_3643,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_956,c_530])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_525,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5534,plain,
    ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_525])).

cnf(c_6353,plain,
    ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5534,c_530])).

cnf(c_6359,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3643,c_6353])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_526,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1287,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_530,c_526])).

cnf(c_6416,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6359,c_1287])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_531,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2352,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_531])).

cnf(c_67,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6018,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2352,c_67])).

cnf(c_6024,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6018,c_530])).

cnf(c_8646,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6416,c_6024])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_519,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2407,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_519])).

cnf(c_2408,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2407,c_813])).

cnf(c_13007,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2408,c_67])).

cnf(c_13008,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13007])).

cnf(c_13036,plain,
    ( k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_8646,c_13008])).

cnf(c_8,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_523,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2626,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_523])).

cnf(c_4312,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2626,c_530])).

cnf(c_4316,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_4312])).

cnf(c_4335,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4316,c_1287])).

cnf(c_5325,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4335,c_530])).

cnf(c_13023,plain,
    ( k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X0) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_5325,c_13008])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_527,plain,
    ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4447,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_530,c_527])).

cnf(c_7648,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_530,c_4447])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_528,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1361,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_530,c_528])).

cnf(c_1362,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1361,c_813])).

cnf(c_6034,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_6024,c_515])).

cnf(c_7654,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_7648,c_813,c_1362,c_6034])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_517,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6040,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_6024,c_517])).

cnf(c_6042,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k9_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_6040,c_1287])).

cnf(c_6038,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_6024,c_528])).

cnf(c_6911,plain,
    ( k8_relat_1(k9_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_6042,c_6038])).

cnf(c_7678,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_7654,c_6911])).

cnf(c_16653,plain,
    ( k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_13023,c_7678])).

cnf(c_17702,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_13036,c_16653])).

cnf(c_17886,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_17702,c_11])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_516,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_950,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_530,c_516])).

cnf(c_951,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_950,c_11])).

cnf(c_19,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_816,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_813,c_19])).

cnf(c_2026,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_951,c_816])).

cnf(c_18558,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_17886,c_2026])).

cnf(c_18560,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_18558,c_17702])).

cnf(c_18561,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_18560])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:40:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 6.76/1.43  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/1.43  
% 6.76/1.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.76/1.43  
% 6.76/1.43  ------  iProver source info
% 6.76/1.43  
% 6.76/1.43  git: date: 2020-06-30 10:37:57 +0100
% 6.76/1.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.76/1.43  git: non_committed_changes: false
% 6.76/1.43  git: last_make_outside_of_git: false
% 6.76/1.43  
% 6.76/1.43  ------ 
% 6.76/1.43  
% 6.76/1.43  ------ Input Options
% 6.76/1.43  
% 6.76/1.43  --out_options                           all
% 6.76/1.43  --tptp_safe_out                         true
% 6.76/1.43  --problem_path                          ""
% 6.76/1.43  --include_path                          ""
% 6.76/1.43  --clausifier                            res/vclausify_rel
% 6.76/1.43  --clausifier_options                    --mode clausify
% 6.76/1.43  --stdin                                 false
% 6.76/1.43  --stats_out                             all
% 6.76/1.43  
% 6.76/1.43  ------ General Options
% 6.76/1.43  
% 6.76/1.43  --fof                                   false
% 6.76/1.43  --time_out_real                         305.
% 6.76/1.43  --time_out_virtual                      -1.
% 6.76/1.43  --symbol_type_check                     false
% 6.76/1.43  --clausify_out                          false
% 6.76/1.43  --sig_cnt_out                           false
% 6.76/1.43  --trig_cnt_out                          false
% 6.76/1.43  --trig_cnt_out_tolerance                1.
% 6.76/1.43  --trig_cnt_out_sk_spl                   false
% 6.76/1.43  --abstr_cl_out                          false
% 6.76/1.43  
% 6.76/1.43  ------ Global Options
% 6.76/1.43  
% 6.76/1.43  --schedule                              default
% 6.76/1.43  --add_important_lit                     false
% 6.76/1.43  --prop_solver_per_cl                    1000
% 6.76/1.43  --min_unsat_core                        false
% 6.76/1.43  --soft_assumptions                      false
% 6.76/1.43  --soft_lemma_size                       3
% 6.76/1.43  --prop_impl_unit_size                   0
% 6.76/1.43  --prop_impl_unit                        []
% 6.76/1.43  --share_sel_clauses                     true
% 6.76/1.43  --reset_solvers                         false
% 6.76/1.43  --bc_imp_inh                            [conj_cone]
% 6.76/1.43  --conj_cone_tolerance                   3.
% 6.76/1.43  --extra_neg_conj                        none
% 6.76/1.43  --large_theory_mode                     true
% 6.76/1.43  --prolific_symb_bound                   200
% 6.76/1.43  --lt_threshold                          2000
% 6.76/1.43  --clause_weak_htbl                      true
% 6.76/1.43  --gc_record_bc_elim                     false
% 6.76/1.43  
% 6.76/1.43  ------ Preprocessing Options
% 6.76/1.43  
% 6.76/1.43  --preprocessing_flag                    true
% 6.76/1.43  --time_out_prep_mult                    0.1
% 6.76/1.43  --splitting_mode                        input
% 6.76/1.43  --splitting_grd                         true
% 6.76/1.43  --splitting_cvd                         false
% 6.76/1.43  --splitting_cvd_svl                     false
% 6.76/1.43  --splitting_nvd                         32
% 6.76/1.43  --sub_typing                            true
% 6.76/1.43  --prep_gs_sim                           true
% 6.76/1.43  --prep_unflatten                        true
% 6.76/1.43  --prep_res_sim                          true
% 6.76/1.43  --prep_upred                            true
% 6.76/1.43  --prep_sem_filter                       exhaustive
% 6.76/1.43  --prep_sem_filter_out                   false
% 6.76/1.43  --pred_elim                             true
% 6.76/1.43  --res_sim_input                         true
% 6.76/1.43  --eq_ax_congr_red                       true
% 6.76/1.43  --pure_diseq_elim                       true
% 6.76/1.43  --brand_transform                       false
% 6.76/1.43  --non_eq_to_eq                          false
% 6.76/1.43  --prep_def_merge                        true
% 6.76/1.43  --prep_def_merge_prop_impl              false
% 6.76/1.43  --prep_def_merge_mbd                    true
% 6.76/1.43  --prep_def_merge_tr_red                 false
% 6.76/1.43  --prep_def_merge_tr_cl                  false
% 6.76/1.43  --smt_preprocessing                     true
% 6.76/1.43  --smt_ac_axioms                         fast
% 6.76/1.43  --preprocessed_out                      false
% 6.76/1.43  --preprocessed_stats                    false
% 6.76/1.43  
% 6.76/1.43  ------ Abstraction refinement Options
% 6.76/1.43  
% 6.76/1.43  --abstr_ref                             []
% 6.76/1.43  --abstr_ref_prep                        false
% 6.76/1.43  --abstr_ref_until_sat                   false
% 6.76/1.43  --abstr_ref_sig_restrict                funpre
% 6.76/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 6.76/1.43  --abstr_ref_under                       []
% 6.76/1.43  
% 6.76/1.43  ------ SAT Options
% 6.76/1.43  
% 6.76/1.43  --sat_mode                              false
% 6.76/1.43  --sat_fm_restart_options                ""
% 6.76/1.43  --sat_gr_def                            false
% 6.76/1.43  --sat_epr_types                         true
% 6.76/1.43  --sat_non_cyclic_types                  false
% 6.76/1.43  --sat_finite_models                     false
% 6.76/1.43  --sat_fm_lemmas                         false
% 6.76/1.43  --sat_fm_prep                           false
% 6.76/1.43  --sat_fm_uc_incr                        true
% 6.76/1.43  --sat_out_model                         small
% 6.76/1.43  --sat_out_clauses                       false
% 6.76/1.43  
% 6.76/1.43  ------ QBF Options
% 6.76/1.43  
% 6.76/1.43  --qbf_mode                              false
% 6.76/1.43  --qbf_elim_univ                         false
% 6.76/1.43  --qbf_dom_inst                          none
% 6.76/1.43  --qbf_dom_pre_inst                      false
% 6.76/1.43  --qbf_sk_in                             false
% 6.76/1.43  --qbf_pred_elim                         true
% 6.76/1.43  --qbf_split                             512
% 6.76/1.43  
% 6.76/1.43  ------ BMC1 Options
% 6.76/1.43  
% 6.76/1.43  --bmc1_incremental                      false
% 6.76/1.43  --bmc1_axioms                           reachable_all
% 6.76/1.43  --bmc1_min_bound                        0
% 6.76/1.43  --bmc1_max_bound                        -1
% 6.76/1.43  --bmc1_max_bound_default                -1
% 6.76/1.43  --bmc1_symbol_reachability              true
% 6.76/1.43  --bmc1_property_lemmas                  false
% 6.76/1.43  --bmc1_k_induction                      false
% 6.76/1.43  --bmc1_non_equiv_states                 false
% 6.76/1.43  --bmc1_deadlock                         false
% 6.76/1.43  --bmc1_ucm                              false
% 6.76/1.43  --bmc1_add_unsat_core                   none
% 6.76/1.43  --bmc1_unsat_core_children              false
% 6.76/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 6.76/1.43  --bmc1_out_stat                         full
% 6.76/1.43  --bmc1_ground_init                      false
% 6.76/1.43  --bmc1_pre_inst_next_state              false
% 6.76/1.43  --bmc1_pre_inst_state                   false
% 6.76/1.43  --bmc1_pre_inst_reach_state             false
% 6.76/1.43  --bmc1_out_unsat_core                   false
% 6.76/1.43  --bmc1_aig_witness_out                  false
% 6.76/1.43  --bmc1_verbose                          false
% 6.76/1.43  --bmc1_dump_clauses_tptp                false
% 6.76/1.43  --bmc1_dump_unsat_core_tptp             false
% 6.76/1.43  --bmc1_dump_file                        -
% 6.76/1.43  --bmc1_ucm_expand_uc_limit              128
% 6.76/1.43  --bmc1_ucm_n_expand_iterations          6
% 6.76/1.43  --bmc1_ucm_extend_mode                  1
% 6.76/1.43  --bmc1_ucm_init_mode                    2
% 6.76/1.43  --bmc1_ucm_cone_mode                    none
% 6.76/1.43  --bmc1_ucm_reduced_relation_type        0
% 6.76/1.43  --bmc1_ucm_relax_model                  4
% 6.76/1.43  --bmc1_ucm_full_tr_after_sat            true
% 6.76/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 6.76/1.43  --bmc1_ucm_layered_model                none
% 6.76/1.43  --bmc1_ucm_max_lemma_size               10
% 6.76/1.43  
% 6.76/1.43  ------ AIG Options
% 6.76/1.43  
% 6.76/1.43  --aig_mode                              false
% 6.76/1.43  
% 6.76/1.43  ------ Instantiation Options
% 6.76/1.43  
% 6.76/1.43  --instantiation_flag                    true
% 6.76/1.43  --inst_sos_flag                         false
% 6.76/1.43  --inst_sos_phase                        true
% 6.76/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.76/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.76/1.43  --inst_lit_sel_side                     num_symb
% 6.76/1.43  --inst_solver_per_active                1400
% 6.76/1.43  --inst_solver_calls_frac                1.
% 6.76/1.43  --inst_passive_queue_type               priority_queues
% 6.76/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.76/1.43  --inst_passive_queues_freq              [25;2]
% 6.76/1.43  --inst_dismatching                      true
% 6.76/1.43  --inst_eager_unprocessed_to_passive     true
% 6.76/1.43  --inst_prop_sim_given                   true
% 6.76/1.43  --inst_prop_sim_new                     false
% 6.76/1.43  --inst_subs_new                         false
% 6.76/1.43  --inst_eq_res_simp                      false
% 6.76/1.43  --inst_subs_given                       false
% 6.76/1.43  --inst_orphan_elimination               true
% 6.76/1.43  --inst_learning_loop_flag               true
% 6.76/1.43  --inst_learning_start                   3000
% 6.76/1.43  --inst_learning_factor                  2
% 6.76/1.43  --inst_start_prop_sim_after_learn       3
% 6.76/1.43  --inst_sel_renew                        solver
% 6.76/1.43  --inst_lit_activity_flag                true
% 6.76/1.43  --inst_restr_to_given                   false
% 6.76/1.43  --inst_activity_threshold               500
% 6.76/1.43  --inst_out_proof                        true
% 6.76/1.43  
% 6.76/1.43  ------ Resolution Options
% 6.76/1.43  
% 6.76/1.43  --resolution_flag                       true
% 6.76/1.43  --res_lit_sel                           adaptive
% 6.76/1.43  --res_lit_sel_side                      none
% 6.76/1.43  --res_ordering                          kbo
% 6.76/1.43  --res_to_prop_solver                    active
% 6.76/1.43  --res_prop_simpl_new                    false
% 6.76/1.43  --res_prop_simpl_given                  true
% 6.76/1.43  --res_passive_queue_type                priority_queues
% 6.76/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.76/1.43  --res_passive_queues_freq               [15;5]
% 6.76/1.43  --res_forward_subs                      full
% 6.76/1.43  --res_backward_subs                     full
% 6.76/1.43  --res_forward_subs_resolution           true
% 6.76/1.43  --res_backward_subs_resolution          true
% 6.76/1.43  --res_orphan_elimination                true
% 6.76/1.43  --res_time_limit                        2.
% 6.76/1.43  --res_out_proof                         true
% 6.76/1.43  
% 6.76/1.43  ------ Superposition Options
% 6.76/1.43  
% 6.76/1.43  --superposition_flag                    true
% 6.76/1.43  --sup_passive_queue_type                priority_queues
% 6.76/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.76/1.43  --sup_passive_queues_freq               [8;1;4]
% 6.76/1.43  --demod_completeness_check              fast
% 6.76/1.43  --demod_use_ground                      true
% 6.76/1.43  --sup_to_prop_solver                    passive
% 6.76/1.43  --sup_prop_simpl_new                    true
% 6.76/1.43  --sup_prop_simpl_given                  true
% 6.76/1.43  --sup_fun_splitting                     false
% 6.76/1.43  --sup_smt_interval                      50000
% 6.76/1.43  
% 6.76/1.43  ------ Superposition Simplification Setup
% 6.76/1.43  
% 6.76/1.43  --sup_indices_passive                   []
% 6.76/1.43  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.76/1.43  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.76/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.76/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 6.76/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.76/1.43  --sup_full_bw                           [BwDemod]
% 6.76/1.43  --sup_immed_triv                        [TrivRules]
% 6.76/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.76/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.76/1.43  --sup_immed_bw_main                     []
% 6.76/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.76/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 6.76/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.76/1.43  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.76/1.43  
% 6.76/1.43  ------ Combination Options
% 6.76/1.43  
% 6.76/1.43  --comb_res_mult                         3
% 6.76/1.43  --comb_sup_mult                         2
% 6.76/1.43  --comb_inst_mult                        10
% 6.76/1.43  
% 6.76/1.43  ------ Debug Options
% 6.76/1.43  
% 6.76/1.43  --dbg_backtrace                         false
% 6.76/1.43  --dbg_dump_prop_clauses                 false
% 6.76/1.43  --dbg_dump_prop_clauses_file            -
% 6.76/1.43  --dbg_out_stat                          false
% 6.76/1.43  ------ Parsing...
% 6.76/1.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.76/1.43  
% 6.76/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.76/1.43  
% 6.76/1.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.76/1.43  
% 6.76/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.76/1.43  ------ Proving...
% 6.76/1.43  ------ Problem Properties 
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  clauses                                 20
% 6.76/1.43  conjectures                             1
% 6.76/1.43  EPR                                     0
% 6.76/1.43  Horn                                    20
% 6.76/1.43  unary                                   4
% 6.76/1.43  binary                                  7
% 6.76/1.43  lits                                    48
% 6.76/1.43  lits eq                                 13
% 6.76/1.43  fd_pure                                 0
% 6.76/1.43  fd_pseudo                               0
% 6.76/1.43  fd_cond                                 0
% 6.76/1.43  fd_pseudo_cond                          0
% 6.76/1.43  AC symbols                              0
% 6.76/1.43  
% 6.76/1.43  ------ Schedule dynamic 5 is on 
% 6.76/1.43  
% 6.76/1.43  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  ------ 
% 6.76/1.43  Current options:
% 6.76/1.43  ------ 
% 6.76/1.43  
% 6.76/1.43  ------ Input Options
% 6.76/1.43  
% 6.76/1.43  --out_options                           all
% 6.76/1.43  --tptp_safe_out                         true
% 6.76/1.43  --problem_path                          ""
% 6.76/1.43  --include_path                          ""
% 6.76/1.43  --clausifier                            res/vclausify_rel
% 6.76/1.43  --clausifier_options                    --mode clausify
% 6.76/1.43  --stdin                                 false
% 6.76/1.43  --stats_out                             all
% 6.76/1.43  
% 6.76/1.43  ------ General Options
% 6.76/1.43  
% 6.76/1.43  --fof                                   false
% 6.76/1.43  --time_out_real                         305.
% 6.76/1.43  --time_out_virtual                      -1.
% 6.76/1.43  --symbol_type_check                     false
% 6.76/1.43  --clausify_out                          false
% 6.76/1.43  --sig_cnt_out                           false
% 6.76/1.43  --trig_cnt_out                          false
% 6.76/1.43  --trig_cnt_out_tolerance                1.
% 6.76/1.43  --trig_cnt_out_sk_spl                   false
% 6.76/1.43  --abstr_cl_out                          false
% 6.76/1.43  
% 6.76/1.43  ------ Global Options
% 6.76/1.43  
% 6.76/1.43  --schedule                              default
% 6.76/1.43  --add_important_lit                     false
% 6.76/1.43  --prop_solver_per_cl                    1000
% 6.76/1.43  --min_unsat_core                        false
% 6.76/1.43  --soft_assumptions                      false
% 6.76/1.43  --soft_lemma_size                       3
% 6.76/1.43  --prop_impl_unit_size                   0
% 6.76/1.43  --prop_impl_unit                        []
% 6.76/1.43  --share_sel_clauses                     true
% 6.76/1.43  --reset_solvers                         false
% 6.76/1.43  --bc_imp_inh                            [conj_cone]
% 6.76/1.43  --conj_cone_tolerance                   3.
% 6.76/1.43  --extra_neg_conj                        none
% 6.76/1.43  --large_theory_mode                     true
% 6.76/1.43  --prolific_symb_bound                   200
% 6.76/1.43  --lt_threshold                          2000
% 6.76/1.43  --clause_weak_htbl                      true
% 6.76/1.43  --gc_record_bc_elim                     false
% 6.76/1.43  
% 6.76/1.43  ------ Preprocessing Options
% 6.76/1.43  
% 6.76/1.43  --preprocessing_flag                    true
% 6.76/1.43  --time_out_prep_mult                    0.1
% 6.76/1.43  --splitting_mode                        input
% 6.76/1.43  --splitting_grd                         true
% 6.76/1.43  --splitting_cvd                         false
% 6.76/1.43  --splitting_cvd_svl                     false
% 6.76/1.43  --splitting_nvd                         32
% 6.76/1.43  --sub_typing                            true
% 6.76/1.43  --prep_gs_sim                           true
% 6.76/1.43  --prep_unflatten                        true
% 6.76/1.43  --prep_res_sim                          true
% 6.76/1.43  --prep_upred                            true
% 6.76/1.43  --prep_sem_filter                       exhaustive
% 6.76/1.43  --prep_sem_filter_out                   false
% 6.76/1.43  --pred_elim                             true
% 6.76/1.43  --res_sim_input                         true
% 6.76/1.43  --eq_ax_congr_red                       true
% 6.76/1.43  --pure_diseq_elim                       true
% 6.76/1.43  --brand_transform                       false
% 6.76/1.43  --non_eq_to_eq                          false
% 6.76/1.43  --prep_def_merge                        true
% 6.76/1.43  --prep_def_merge_prop_impl              false
% 6.76/1.43  --prep_def_merge_mbd                    true
% 6.76/1.43  --prep_def_merge_tr_red                 false
% 6.76/1.43  --prep_def_merge_tr_cl                  false
% 6.76/1.43  --smt_preprocessing                     true
% 6.76/1.43  --smt_ac_axioms                         fast
% 6.76/1.43  --preprocessed_out                      false
% 6.76/1.43  --preprocessed_stats                    false
% 6.76/1.43  
% 6.76/1.43  ------ Abstraction refinement Options
% 6.76/1.43  
% 6.76/1.43  --abstr_ref                             []
% 6.76/1.43  --abstr_ref_prep                        false
% 6.76/1.43  --abstr_ref_until_sat                   false
% 6.76/1.43  --abstr_ref_sig_restrict                funpre
% 6.76/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 6.76/1.43  --abstr_ref_under                       []
% 6.76/1.43  
% 6.76/1.43  ------ SAT Options
% 6.76/1.43  
% 6.76/1.43  --sat_mode                              false
% 6.76/1.43  --sat_fm_restart_options                ""
% 6.76/1.43  --sat_gr_def                            false
% 6.76/1.43  --sat_epr_types                         true
% 6.76/1.43  --sat_non_cyclic_types                  false
% 6.76/1.43  --sat_finite_models                     false
% 6.76/1.43  --sat_fm_lemmas                         false
% 6.76/1.43  --sat_fm_prep                           false
% 6.76/1.43  --sat_fm_uc_incr                        true
% 6.76/1.43  --sat_out_model                         small
% 6.76/1.43  --sat_out_clauses                       false
% 6.76/1.43  
% 6.76/1.43  ------ QBF Options
% 6.76/1.43  
% 6.76/1.43  --qbf_mode                              false
% 6.76/1.43  --qbf_elim_univ                         false
% 6.76/1.43  --qbf_dom_inst                          none
% 6.76/1.43  --qbf_dom_pre_inst                      false
% 6.76/1.43  --qbf_sk_in                             false
% 6.76/1.43  --qbf_pred_elim                         true
% 6.76/1.43  --qbf_split                             512
% 6.76/1.43  
% 6.76/1.43  ------ BMC1 Options
% 6.76/1.43  
% 6.76/1.43  --bmc1_incremental                      false
% 6.76/1.43  --bmc1_axioms                           reachable_all
% 6.76/1.43  --bmc1_min_bound                        0
% 6.76/1.43  --bmc1_max_bound                        -1
% 6.76/1.43  --bmc1_max_bound_default                -1
% 6.76/1.43  --bmc1_symbol_reachability              true
% 6.76/1.43  --bmc1_property_lemmas                  false
% 6.76/1.43  --bmc1_k_induction                      false
% 6.76/1.43  --bmc1_non_equiv_states                 false
% 6.76/1.43  --bmc1_deadlock                         false
% 6.76/1.43  --bmc1_ucm                              false
% 6.76/1.43  --bmc1_add_unsat_core                   none
% 6.76/1.43  --bmc1_unsat_core_children              false
% 6.76/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 6.76/1.43  --bmc1_out_stat                         full
% 6.76/1.43  --bmc1_ground_init                      false
% 6.76/1.43  --bmc1_pre_inst_next_state              false
% 6.76/1.43  --bmc1_pre_inst_state                   false
% 6.76/1.43  --bmc1_pre_inst_reach_state             false
% 6.76/1.43  --bmc1_out_unsat_core                   false
% 6.76/1.43  --bmc1_aig_witness_out                  false
% 6.76/1.43  --bmc1_verbose                          false
% 6.76/1.43  --bmc1_dump_clauses_tptp                false
% 6.76/1.43  --bmc1_dump_unsat_core_tptp             false
% 6.76/1.43  --bmc1_dump_file                        -
% 6.76/1.43  --bmc1_ucm_expand_uc_limit              128
% 6.76/1.43  --bmc1_ucm_n_expand_iterations          6
% 6.76/1.43  --bmc1_ucm_extend_mode                  1
% 6.76/1.43  --bmc1_ucm_init_mode                    2
% 6.76/1.43  --bmc1_ucm_cone_mode                    none
% 6.76/1.43  --bmc1_ucm_reduced_relation_type        0
% 6.76/1.43  --bmc1_ucm_relax_model                  4
% 6.76/1.43  --bmc1_ucm_full_tr_after_sat            true
% 6.76/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 6.76/1.43  --bmc1_ucm_layered_model                none
% 6.76/1.43  --bmc1_ucm_max_lemma_size               10
% 6.76/1.43  
% 6.76/1.43  ------ AIG Options
% 6.76/1.43  
% 6.76/1.43  --aig_mode                              false
% 6.76/1.43  
% 6.76/1.43  ------ Instantiation Options
% 6.76/1.43  
% 6.76/1.43  --instantiation_flag                    true
% 6.76/1.43  --inst_sos_flag                         false
% 6.76/1.43  --inst_sos_phase                        true
% 6.76/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.76/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.76/1.43  --inst_lit_sel_side                     none
% 6.76/1.43  --inst_solver_per_active                1400
% 6.76/1.43  --inst_solver_calls_frac                1.
% 6.76/1.43  --inst_passive_queue_type               priority_queues
% 6.76/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.76/1.43  --inst_passive_queues_freq              [25;2]
% 6.76/1.43  --inst_dismatching                      true
% 6.76/1.43  --inst_eager_unprocessed_to_passive     true
% 6.76/1.43  --inst_prop_sim_given                   true
% 6.76/1.43  --inst_prop_sim_new                     false
% 6.76/1.43  --inst_subs_new                         false
% 6.76/1.43  --inst_eq_res_simp                      false
% 6.76/1.43  --inst_subs_given                       false
% 6.76/1.43  --inst_orphan_elimination               true
% 6.76/1.43  --inst_learning_loop_flag               true
% 6.76/1.43  --inst_learning_start                   3000
% 6.76/1.43  --inst_learning_factor                  2
% 6.76/1.43  --inst_start_prop_sim_after_learn       3
% 6.76/1.43  --inst_sel_renew                        solver
% 6.76/1.43  --inst_lit_activity_flag                true
% 6.76/1.43  --inst_restr_to_given                   false
% 6.76/1.43  --inst_activity_threshold               500
% 6.76/1.43  --inst_out_proof                        true
% 6.76/1.43  
% 6.76/1.43  ------ Resolution Options
% 6.76/1.43  
% 6.76/1.43  --resolution_flag                       false
% 6.76/1.43  --res_lit_sel                           adaptive
% 6.76/1.43  --res_lit_sel_side                      none
% 6.76/1.43  --res_ordering                          kbo
% 6.76/1.43  --res_to_prop_solver                    active
% 6.76/1.43  --res_prop_simpl_new                    false
% 6.76/1.43  --res_prop_simpl_given                  true
% 6.76/1.43  --res_passive_queue_type                priority_queues
% 6.76/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.76/1.43  --res_passive_queues_freq               [15;5]
% 6.76/1.43  --res_forward_subs                      full
% 6.76/1.43  --res_backward_subs                     full
% 6.76/1.43  --res_forward_subs_resolution           true
% 6.76/1.43  --res_backward_subs_resolution          true
% 6.76/1.43  --res_orphan_elimination                true
% 6.76/1.43  --res_time_limit                        2.
% 6.76/1.43  --res_out_proof                         true
% 6.76/1.43  
% 6.76/1.43  ------ Superposition Options
% 6.76/1.43  
% 6.76/1.43  --superposition_flag                    true
% 6.76/1.43  --sup_passive_queue_type                priority_queues
% 6.76/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.76/1.43  --sup_passive_queues_freq               [8;1;4]
% 6.76/1.43  --demod_completeness_check              fast
% 6.76/1.43  --demod_use_ground                      true
% 6.76/1.43  --sup_to_prop_solver                    passive
% 6.76/1.43  --sup_prop_simpl_new                    true
% 6.76/1.43  --sup_prop_simpl_given                  true
% 6.76/1.43  --sup_fun_splitting                     false
% 6.76/1.43  --sup_smt_interval                      50000
% 6.76/1.43  
% 6.76/1.43  ------ Superposition Simplification Setup
% 6.76/1.43  
% 6.76/1.43  --sup_indices_passive                   []
% 6.76/1.43  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.76/1.43  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.76/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.76/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 6.76/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.76/1.43  --sup_full_bw                           [BwDemod]
% 6.76/1.43  --sup_immed_triv                        [TrivRules]
% 6.76/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.76/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.76/1.43  --sup_immed_bw_main                     []
% 6.76/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.76/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 6.76/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.76/1.43  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.76/1.43  
% 6.76/1.43  ------ Combination Options
% 6.76/1.43  
% 6.76/1.43  --comb_res_mult                         3
% 6.76/1.43  --comb_sup_mult                         2
% 6.76/1.43  --comb_inst_mult                        10
% 6.76/1.43  
% 6.76/1.43  ------ Debug Options
% 6.76/1.43  
% 6.76/1.43  --dbg_backtrace                         false
% 6.76/1.43  --dbg_dump_prop_clauses                 false
% 6.76/1.43  --dbg_dump_prop_clauses_file            -
% 6.76/1.43  --dbg_out_stat                          false
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  ------ Proving...
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  % SZS status Theorem for theBenchmark.p
% 6.76/1.43  
% 6.76/1.43   Resolution empty clause
% 6.76/1.43  
% 6.76/1.43  % SZS output start CNFRefutation for theBenchmark.p
% 6.76/1.43  
% 6.76/1.43  fof(f9,axiom,(
% 6.76/1.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f55,plain,(
% 6.76/1.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.76/1.43    inference(cnf_transformation,[],[f9])).
% 6.76/1.43  
% 6.76/1.43  fof(f23,axiom,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f43,plain,(
% 6.76/1.43    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f23])).
% 6.76/1.43  
% 6.76/1.43  fof(f72,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f43])).
% 6.76/1.43  
% 6.76/1.43  fof(f18,axiom,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f36,plain,(
% 6.76/1.43    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f18])).
% 6.76/1.43  
% 6.76/1.43  fof(f66,plain,(
% 6.76/1.43    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f36])).
% 6.76/1.43  
% 6.76/1.43  fof(f17,axiom,(
% 6.76/1.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f65,plain,(
% 6.76/1.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 6.76/1.43    inference(cnf_transformation,[],[f17])).
% 6.76/1.43  
% 6.76/1.43  fof(f14,axiom,(
% 6.76/1.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f32,plain,(
% 6.76/1.43    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.76/1.43    inference(ennf_transformation,[],[f14])).
% 6.76/1.43  
% 6.76/1.43  fof(f33,plain,(
% 6.76/1.43    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.76/1.43    inference(flattening,[],[f32])).
% 6.76/1.43  
% 6.76/1.43  fof(f61,plain,(
% 6.76/1.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f33])).
% 6.76/1.43  
% 6.76/1.43  fof(f13,axiom,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f31,plain,(
% 6.76/1.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f13])).
% 6.76/1.43  
% 6.76/1.43  fof(f59,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f31])).
% 6.76/1.43  
% 6.76/1.43  fof(f8,axiom,(
% 6.76/1.43    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f26,plain,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 6.76/1.43    inference(ennf_transformation,[],[f8])).
% 6.76/1.43  
% 6.76/1.43  fof(f27,plain,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 6.76/1.43    inference(flattening,[],[f26])).
% 6.76/1.43  
% 6.76/1.43  fof(f54,plain,(
% 6.76/1.43    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f27])).
% 6.76/1.43  
% 6.76/1.43  fof(f64,plain,(
% 6.76/1.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.76/1.43    inference(cnf_transformation,[],[f17])).
% 6.76/1.43  
% 6.76/1.43  fof(f19,axiom,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f37,plain,(
% 6.76/1.43    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f19])).
% 6.76/1.43  
% 6.76/1.43  fof(f38,plain,(
% 6.76/1.43    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(flattening,[],[f37])).
% 6.76/1.43  
% 6.76/1.43  fof(f68,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f38])).
% 6.76/1.43  
% 6.76/1.43  fof(f15,axiom,(
% 6.76/1.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f34,plain,(
% 6.76/1.43    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.76/1.43    inference(ennf_transformation,[],[f15])).
% 6.76/1.43  
% 6.76/1.43  fof(f62,plain,(
% 6.76/1.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f34])).
% 6.76/1.43  
% 6.76/1.43  fof(f12,axiom,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f30,plain,(
% 6.76/1.43    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f12])).
% 6.76/1.43  
% 6.76/1.43  fof(f58,plain,(
% 6.76/1.43    ( ! [X2,X0,X1] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f30])).
% 6.76/1.43  
% 6.76/1.43  fof(f11,axiom,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f29,plain,(
% 6.76/1.43    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f11])).
% 6.76/1.43  
% 6.76/1.43  fof(f57,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f29])).
% 6.76/1.43  
% 6.76/1.43  fof(f21,axiom,(
% 6.76/1.43    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f41,plain,(
% 6.76/1.43    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 6.76/1.43    inference(ennf_transformation,[],[f21])).
% 6.76/1.43  
% 6.76/1.43  fof(f70,plain,(
% 6.76/1.43    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f41])).
% 6.76/1.43  
% 6.76/1.43  fof(f22,axiom,(
% 6.76/1.43    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f42,plain,(
% 6.76/1.43    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f22])).
% 6.76/1.43  
% 6.76/1.43  fof(f71,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f42])).
% 6.76/1.43  
% 6.76/1.43  fof(f7,axiom,(
% 6.76/1.43    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f53,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f7])).
% 6.76/1.43  
% 6.76/1.43  fof(f1,axiom,(
% 6.76/1.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f47,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f1])).
% 6.76/1.43  
% 6.76/1.43  fof(f2,axiom,(
% 6.76/1.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f48,plain,(
% 6.76/1.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f2])).
% 6.76/1.43  
% 6.76/1.43  fof(f3,axiom,(
% 6.76/1.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f49,plain,(
% 6.76/1.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f3])).
% 6.76/1.43  
% 6.76/1.43  fof(f4,axiom,(
% 6.76/1.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f50,plain,(
% 6.76/1.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f4])).
% 6.76/1.43  
% 6.76/1.43  fof(f5,axiom,(
% 6.76/1.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f51,plain,(
% 6.76/1.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f5])).
% 6.76/1.43  
% 6.76/1.43  fof(f6,axiom,(
% 6.76/1.43    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f52,plain,(
% 6.76/1.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.76/1.43    inference(cnf_transformation,[],[f6])).
% 6.76/1.43  
% 6.76/1.43  fof(f74,plain,(
% 6.76/1.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.76/1.43    inference(definition_unfolding,[],[f51,f52])).
% 6.76/1.43  
% 6.76/1.43  fof(f75,plain,(
% 6.76/1.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.76/1.43    inference(definition_unfolding,[],[f50,f74])).
% 6.76/1.43  
% 6.76/1.43  fof(f76,plain,(
% 6.76/1.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.76/1.43    inference(definition_unfolding,[],[f49,f75])).
% 6.76/1.43  
% 6.76/1.43  fof(f77,plain,(
% 6.76/1.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.76/1.43    inference(definition_unfolding,[],[f48,f76])).
% 6.76/1.43  
% 6.76/1.43  fof(f78,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.76/1.43    inference(definition_unfolding,[],[f47,f77])).
% 6.76/1.43  
% 6.76/1.43  fof(f79,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 6.76/1.43    inference(definition_unfolding,[],[f53,f78])).
% 6.76/1.43  
% 6.76/1.43  fof(f80,plain,(
% 6.76/1.43    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.76/1.43    inference(definition_unfolding,[],[f71,f79])).
% 6.76/1.43  
% 6.76/1.43  fof(f24,conjecture,(
% 6.76/1.43    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 6.76/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.76/1.43  
% 6.76/1.43  fof(f25,negated_conjecture,(
% 6.76/1.43    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 6.76/1.43    inference(negated_conjecture,[],[f24])).
% 6.76/1.43  
% 6.76/1.43  fof(f44,plain,(
% 6.76/1.43    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 6.76/1.43    inference(ennf_transformation,[],[f25])).
% 6.76/1.43  
% 6.76/1.43  fof(f45,plain,(
% 6.76/1.43    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 6.76/1.43    introduced(choice_axiom,[])).
% 6.76/1.43  
% 6.76/1.43  fof(f46,plain,(
% 6.76/1.43    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 6.76/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f45])).
% 6.76/1.43  
% 6.76/1.43  fof(f73,plain,(
% 6.76/1.43    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 6.76/1.43    inference(cnf_transformation,[],[f46])).
% 6.76/1.43  
% 6.76/1.43  fof(f81,plain,(
% 6.76/1.43    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 6.76/1.43    inference(definition_unfolding,[],[f73,f79])).
% 6.76/1.43  
% 6.76/1.43  cnf(c_1,plain,
% 6.76/1.43      ( v1_relat_1(k6_relat_1(X0)) ),
% 6.76/1.43      inference(cnf_transformation,[],[f55]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_530,plain,
% 6.76/1.43      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_18,plain,
% 6.76/1.43      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 6.76/1.43      inference(cnf_transformation,[],[f72]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_515,plain,
% 6.76/1.43      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 6.76/1.43      | v1_relat_1(X1) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_813,plain,
% 6.76/1.43      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_530,c_515]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_13,plain,
% 6.76/1.43      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 6.76/1.43      inference(cnf_transformation,[],[f66]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_520,plain,
% 6.76/1.43      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 6.76/1.43      | v1_relat_1(X0) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_956,plain,
% 6.76/1.43      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_813,c_520]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_3643,plain,
% 6.76/1.43      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
% 6.76/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_956,c_530]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_10,plain,
% 6.76/1.43      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 6.76/1.43      inference(cnf_transformation,[],[f65]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6,plain,
% 6.76/1.43      ( ~ r1_tarski(X0,X1)
% 6.76/1.43      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 6.76/1.43      | ~ v1_relat_1(X1)
% 6.76/1.43      | ~ v1_relat_1(X0) ),
% 6.76/1.43      inference(cnf_transformation,[],[f61]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_525,plain,
% 6.76/1.43      ( r1_tarski(X0,X1) != iProver_top
% 6.76/1.43      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 6.76/1.43      | v1_relat_1(X0) != iProver_top
% 6.76/1.43      | v1_relat_1(X1) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_5534,plain,
% 6.76/1.43      ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
% 6.76/1.43      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 6.76/1.43      | v1_relat_1(X0) != iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_10,c_525]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6353,plain,
% 6.76/1.43      ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
% 6.76/1.43      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 6.76/1.43      | v1_relat_1(X0) != iProver_top ),
% 6.76/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_5534,c_530]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6359,plain,
% 6.76/1.43      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
% 6.76/1.43      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_3643,c_6353]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_5,plain,
% 6.76/1.43      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 6.76/1.43      inference(cnf_transformation,[],[f59]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_526,plain,
% 6.76/1.43      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 6.76/1.43      | v1_relat_1(X0) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_1287,plain,
% 6.76/1.43      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_530,c_526]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6416,plain,
% 6.76/1.43      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 6.76/1.43      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 6.76/1.43      inference(light_normalisation,[status(thm)],[c_6359,c_1287]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_0,plain,
% 6.76/1.43      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 6.76/1.43      inference(cnf_transformation,[],[f54]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_531,plain,
% 6.76/1.43      ( v1_relat_1(X0) != iProver_top
% 6.76/1.43      | v1_relat_1(X1) != iProver_top
% 6.76/1.43      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_2352,plain,
% 6.76/1.43      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_813,c_531]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_67,plain,
% 6.76/1.43      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6018,plain,
% 6.76/1.43      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(global_propositional_subsumption,[status(thm)],[c_2352,c_67]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6024,plain,
% 6.76/1.43      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 6.76/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_6018,c_530]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_8646,plain,
% 6.76/1.43      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) = iProver_top ),
% 6.76/1.43      inference(global_propositional_subsumption,[status(thm)],[c_6416,c_6024]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_11,plain,
% 6.76/1.43      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 6.76/1.43      inference(cnf_transformation,[],[f64]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_14,plain,
% 6.76/1.43      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 6.76/1.43      | ~ v1_relat_1(X0)
% 6.76/1.43      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 6.76/1.43      inference(cnf_transformation,[],[f68]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_519,plain,
% 6.76/1.43      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 6.76/1.43      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 6.76/1.43      | v1_relat_1(X1) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_2407,plain,
% 6.76/1.43      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 6.76/1.43      | r1_tarski(X1,X0) != iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_11,c_519]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_2408,plain,
% 6.76/1.43      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 6.76/1.43      | r1_tarski(X0,X1) != iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 6.76/1.43      inference(demodulation,[status(thm)],[c_2407,c_813]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_13007,plain,
% 6.76/1.43      ( r1_tarski(X0,X1) != iProver_top
% 6.76/1.43      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 6.76/1.43      inference(global_propositional_subsumption,[status(thm)],[c_2408,c_67]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_13008,plain,
% 6.76/1.43      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 6.76/1.43      | r1_tarski(X0,X1) != iProver_top ),
% 6.76/1.43      inference(renaming,[status(thm)],[c_13007]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_13036,plain,
% 6.76/1.43      ( k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_8646,c_13008]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_8,plain,
% 6.76/1.43      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 6.76/1.43      | ~ v1_relat_1(X1)
% 6.76/1.43      | ~ v1_relat_1(X0) ),
% 6.76/1.43      inference(cnf_transformation,[],[f62]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_523,plain,
% 6.76/1.43      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 6.76/1.43      | v1_relat_1(X0) != iProver_top
% 6.76/1.43      | v1_relat_1(X1) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_2626,plain,
% 6.76/1.43      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
% 6.76/1.43      | v1_relat_1(X0) != iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_10,c_523]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_4312,plain,
% 6.76/1.43      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
% 6.76/1.43      | v1_relat_1(X0) != iProver_top ),
% 6.76/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_2626,c_530]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_4316,plain,
% 6.76/1.43      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_813,c_4312]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_4335,plain,
% 6.76/1.43      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 6.76/1.43      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.76/1.43      inference(light_normalisation,[status(thm)],[c_4316,c_1287]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_5325,plain,
% 6.76/1.43      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 6.76/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_4335,c_530]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_13023,plain,
% 6.76/1.43      ( k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X0) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_5325,c_13008]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_4,plain,
% 6.76/1.43      ( ~ v1_relat_1(X0)
% 6.76/1.43      | ~ v1_relat_1(X1)
% 6.76/1.43      | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
% 6.76/1.43      inference(cnf_transformation,[],[f58]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_527,plain,
% 6.76/1.43      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
% 6.76/1.43      | v1_relat_1(X1) != iProver_top
% 6.76/1.43      | v1_relat_1(X2) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_4447,plain,
% 6.76/1.43      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
% 6.76/1.43      | v1_relat_1(X2) != iProver_top ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_530,c_527]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_7648,plain,
% 6.76/1.43      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_530,c_4447]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_3,plain,
% 6.76/1.43      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 6.76/1.43      inference(cnf_transformation,[],[f57]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_528,plain,
% 6.76/1.43      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 6.76/1.43      | v1_relat_1(X0) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_1361,plain,
% 6.76/1.43      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_530,c_528]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_1362,plain,
% 6.76/1.43      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(light_normalisation,[status(thm)],[c_1361,c_813]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6034,plain,
% 6.76/1.43      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_6024,c_515]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_7654,plain,
% 6.76/1.43      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 6.76/1.43      inference(demodulation,[status(thm)],[c_7648,c_813,c_1362,c_6034]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_16,plain,
% 6.76/1.43      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 6.76/1.43      inference(cnf_transformation,[],[f70]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_517,plain,
% 6.76/1.43      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 6.76/1.43      | v1_relat_1(X0) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6040,plain,
% 6.76/1.43      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_6024,c_517]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6042,plain,
% 6.76/1.43      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k9_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(light_normalisation,[status(thm)],[c_6040,c_1287]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6038,plain,
% 6.76/1.43      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_6024,c_528]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_6911,plain,
% 6.76/1.43      ( k8_relat_1(k9_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_6042,c_6038]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_7678,plain,
% 6.76/1.43      ( k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_7654,c_6911]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_16653,plain,
% 6.76/1.43      ( k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(demodulation,[status(thm)],[c_13023,c_7678]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_17702,plain,
% 6.76/1.43      ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(light_normalisation,[status(thm)],[c_13036,c_16653]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_17886,plain,
% 6.76/1.43      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_17702,c_11]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_17,plain,
% 6.76/1.43      ( ~ v1_relat_1(X0)
% 6.76/1.43      | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 6.76/1.43      inference(cnf_transformation,[],[f80]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_516,plain,
% 6.76/1.43      ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 6.76/1.43      | v1_relat_1(X0) != iProver_top ),
% 6.76/1.43      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_950,plain,
% 6.76/1.43      ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.76/1.43      inference(superposition,[status(thm)],[c_530,c_516]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_951,plain,
% 6.76/1.43      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.76/1.43      inference(light_normalisation,[status(thm)],[c_950,c_11]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_19,negated_conjecture,
% 6.76/1.43      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 6.76/1.43      inference(cnf_transformation,[],[f81]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_816,plain,
% 6.76/1.43      ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 6.76/1.43      inference(demodulation,[status(thm)],[c_813,c_19]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_2026,plain,
% 6.76/1.43      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 6.76/1.43      inference(demodulation,[status(thm)],[c_951,c_816]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_18558,plain,
% 6.76/1.43      ( k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 6.76/1.43      inference(demodulation,[status(thm)],[c_17886,c_2026]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_18560,plain,
% 6.76/1.43      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 6.76/1.43      inference(demodulation,[status(thm)],[c_18558,c_17702]) ).
% 6.76/1.43  
% 6.76/1.43  cnf(c_18561,plain,
% 6.76/1.43      ( $false ),
% 6.76/1.43      inference(equality_resolution_simp,[status(thm)],[c_18560]) ).
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  % SZS output end CNFRefutation for theBenchmark.p
% 6.76/1.43  
% 6.76/1.43  ------                               Statistics
% 6.76/1.43  
% 6.76/1.43  ------ General
% 6.76/1.43  
% 6.76/1.43  abstr_ref_over_cycles:                  0
% 6.76/1.43  abstr_ref_under_cycles:                 0
% 6.76/1.43  gc_basic_clause_elim:                   0
% 6.76/1.43  forced_gc_time:                         0
% 6.76/1.43  parsing_time:                           0.009
% 6.76/1.43  unif_index_cands_time:                  0.
% 6.76/1.43  unif_index_add_time:                    0.
% 6.76/1.43  orderings_time:                         0.
% 6.76/1.43  out_proof_time:                         0.01
% 6.76/1.43  total_time:                             0.54
% 6.76/1.43  num_of_symbols:                         44
% 6.76/1.43  num_of_terms:                           26436
% 6.76/1.43  
% 6.76/1.43  ------ Preprocessing
% 6.76/1.43  
% 6.76/1.43  num_of_splits:                          0
% 6.76/1.43  num_of_split_atoms:                     0
% 6.76/1.43  num_of_reused_defs:                     0
% 6.76/1.43  num_eq_ax_congr_red:                    8
% 6.76/1.43  num_of_sem_filtered_clauses:            1
% 6.76/1.43  num_of_subtypes:                        0
% 6.76/1.43  monotx_restored_types:                  0
% 6.76/1.43  sat_num_of_epr_types:                   0
% 6.76/1.43  sat_num_of_non_cyclic_types:            0
% 6.76/1.43  sat_guarded_non_collapsed_types:        0
% 6.76/1.43  num_pure_diseq_elim:                    0
% 6.76/1.43  simp_replaced_by:                       0
% 6.76/1.43  res_preprocessed:                       85
% 6.76/1.43  prep_upred:                             0
% 6.76/1.43  prep_unflattend:                        0
% 6.76/1.43  smt_new_axioms:                         0
% 6.76/1.43  pred_elim_cands:                        2
% 6.76/1.43  pred_elim:                              0
% 6.76/1.43  pred_elim_cl:                           0
% 6.76/1.43  pred_elim_cycles:                       1
% 6.76/1.43  merged_defs:                            0
% 6.76/1.43  merged_defs_ncl:                        0
% 6.76/1.43  bin_hyper_res:                          0
% 6.76/1.43  prep_cycles:                            3
% 6.76/1.43  pred_elim_time:                         0.
% 6.76/1.43  splitting_time:                         0.
% 6.76/1.43  sem_filter_time:                        0.
% 6.76/1.43  monotx_time:                            0.
% 6.76/1.43  subtype_inf_time:                       0.
% 6.76/1.43  
% 6.76/1.43  ------ Problem properties
% 6.76/1.43  
% 6.76/1.43  clauses:                                20
% 6.76/1.43  conjectures:                            1
% 6.76/1.43  epr:                                    0
% 6.76/1.43  horn:                                   20
% 6.76/1.43  ground:                                 1
% 6.76/1.43  unary:                                  4
% 6.76/1.43  binary:                                 7
% 6.76/1.43  lits:                                   48
% 6.76/1.43  lits_eq:                                13
% 6.76/1.43  fd_pure:                                0
% 6.76/1.43  fd_pseudo:                              0
% 6.76/1.43  fd_cond:                                0
% 6.76/1.43  fd_pseudo_cond:                         0
% 6.76/1.43  ac_symbols:                             0
% 6.76/1.43  
% 6.76/1.43  ------ Propositional Solver
% 6.76/1.43  
% 6.76/1.43  prop_solver_calls:                      25
% 6.76/1.43  prop_fast_solver_calls:                 696
% 6.76/1.43  smt_solver_calls:                       0
% 6.76/1.43  smt_fast_solver_calls:                  0
% 6.76/1.43  prop_num_of_clauses:                    6998
% 6.76/1.43  prop_preprocess_simplified:             12691
% 6.76/1.43  prop_fo_subsumed:                       9
% 6.76/1.43  prop_solver_time:                       0.
% 6.76/1.43  smt_solver_time:                        0.
% 6.76/1.43  smt_fast_solver_time:                   0.
% 6.76/1.43  prop_fast_solver_time:                  0.
% 6.76/1.43  prop_unsat_core_time:                   0.
% 6.76/1.43  
% 6.76/1.43  ------ QBF
% 6.76/1.43  
% 6.76/1.43  qbf_q_res:                              0
% 6.76/1.43  qbf_num_tautologies:                    0
% 6.76/1.43  qbf_prep_cycles:                        0
% 6.76/1.43  
% 6.76/1.43  ------ BMC1
% 6.76/1.43  
% 6.76/1.43  bmc1_current_bound:                     -1
% 6.76/1.43  bmc1_last_solved_bound:                 -1
% 6.76/1.43  bmc1_unsat_core_size:                   -1
% 6.76/1.43  bmc1_unsat_core_parents_size:           -1
% 6.76/1.43  bmc1_merge_next_fun:                    0
% 6.76/1.43  bmc1_unsat_core_clauses_time:           0.
% 6.76/1.43  
% 6.76/1.43  ------ Instantiation
% 6.76/1.43  
% 6.76/1.43  inst_num_of_clauses:                    1798
% 6.76/1.43  inst_num_in_passive:                    442
% 6.76/1.43  inst_num_in_active:                     712
% 6.76/1.43  inst_num_in_unprocessed:                644
% 6.76/1.43  inst_num_of_loops:                      760
% 6.76/1.43  inst_num_of_learning_restarts:          0
% 6.76/1.43  inst_num_moves_active_passive:          47
% 6.76/1.43  inst_lit_activity:                      0
% 6.76/1.43  inst_lit_activity_moves:                1
% 6.76/1.43  inst_num_tautologies:                   0
% 6.76/1.43  inst_num_prop_implied:                  0
% 6.76/1.43  inst_num_existing_simplified:           0
% 6.76/1.43  inst_num_eq_res_simplified:             0
% 6.76/1.43  inst_num_child_elim:                    0
% 6.76/1.43  inst_num_of_dismatching_blockings:      1151
% 6.76/1.43  inst_num_of_non_proper_insts:           1226
% 6.76/1.43  inst_num_of_duplicates:                 0
% 6.76/1.43  inst_inst_num_from_inst_to_res:         0
% 6.76/1.43  inst_dismatching_checking_time:         0.
% 6.76/1.43  
% 6.76/1.43  ------ Resolution
% 6.76/1.43  
% 6.76/1.43  res_num_of_clauses:                     0
% 6.76/1.43  res_num_in_passive:                     0
% 6.76/1.43  res_num_in_active:                      0
% 6.76/1.43  res_num_of_loops:                       88
% 6.76/1.43  res_forward_subset_subsumed:            163
% 6.76/1.43  res_backward_subset_subsumed:           0
% 6.76/1.43  res_forward_subsumed:                   0
% 6.76/1.43  res_backward_subsumed:                  0
% 6.76/1.43  res_forward_subsumption_resolution:     0
% 6.76/1.43  res_backward_subsumption_resolution:    0
% 6.76/1.43  res_clause_to_clause_subsumption:       4606
% 6.76/1.43  res_orphan_elimination:                 0
% 6.76/1.43  res_tautology_del:                      108
% 6.76/1.43  res_num_eq_res_simplified:              0
% 6.76/1.43  res_num_sel_changes:                    0
% 6.76/1.43  res_moves_from_active_to_pass:          0
% 6.76/1.43  
% 6.76/1.43  ------ Superposition
% 6.76/1.43  
% 6.76/1.43  sup_time_total:                         0.
% 6.76/1.43  sup_time_generating:                    0.
% 6.76/1.43  sup_time_sim_full:                      0.
% 6.76/1.43  sup_time_sim_immed:                     0.
% 6.76/1.43  
% 6.76/1.43  sup_num_of_clauses:                     721
% 6.76/1.43  sup_num_in_active:                      101
% 6.76/1.43  sup_num_in_passive:                     620
% 6.76/1.43  sup_num_of_loops:                       151
% 6.76/1.43  sup_fw_superposition:                   1256
% 6.76/1.43  sup_bw_superposition:                   1128
% 6.76/1.43  sup_immediate_simplified:               1319
% 6.76/1.43  sup_given_eliminated:                   0
% 6.76/1.43  comparisons_done:                       0
% 6.76/1.43  comparisons_avoided:                    0
% 6.76/1.43  
% 6.76/1.43  ------ Simplifications
% 6.76/1.43  
% 6.76/1.43  
% 6.76/1.43  sim_fw_subset_subsumed:                 5
% 6.76/1.43  sim_bw_subset_subsumed:                 10
% 6.76/1.43  sim_fw_subsumed:                        442
% 6.76/1.43  sim_bw_subsumed:                        3
% 6.76/1.43  sim_fw_subsumption_res:                 9
% 6.76/1.43  sim_bw_subsumption_res:                 0
% 6.76/1.43  sim_tautology_del:                      3
% 6.76/1.43  sim_eq_tautology_del:                   183
% 6.76/1.43  sim_eq_res_simp:                        0
% 6.76/1.43  sim_fw_demodulated:                     547
% 6.76/1.43  sim_bw_demodulated:                     57
% 6.76/1.43  sim_light_normalised:                   523
% 6.76/1.43  sim_joinable_taut:                      0
% 6.76/1.43  sim_joinable_simp:                      0
% 6.76/1.43  sim_ac_normalised:                      0
% 6.76/1.43  sim_smt_subsumption:                    0
% 6.76/1.43  
%------------------------------------------------------------------------------
