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
% DateTime   : Thu Dec  3 11:49:56 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :  159 (9208 expanded)
%              Number of clauses        :   86 (3515 expanded)
%              Number of leaves         :   23 (2149 expanded)
%              Depth                    :   24
%              Number of atoms          :  254 (12766 expanded)
%              Number of equality atoms :  173 (8498 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f48])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f63,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f72])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f48,f76])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f49,f76,f76])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f24,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f24])).

fof(f39,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f25])).

fof(f42,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f42])).

fof(f71,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f71,f48])).

cnf(c_7,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_586,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_585,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1879,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_586,c_585])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_576,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1370,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_586,c_576])).

cnf(c_2407,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_1879,c_1370])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_577,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_933,plain,
    ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_586,c_577])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_934,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_933,c_12])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_588,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1235,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_934,c_588])).

cnf(c_2588,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2407,c_1235])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_579,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1886,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_579])).

cnf(c_1890,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1886,c_1370])).

cnf(c_5202,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1890,c_2407])).

cnf(c_5206,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5202,c_586])).

cnf(c_5213,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_2588,c_5206])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_587,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2305,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_587])).

cnf(c_53,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10676,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2305,c_53])).

cnf(c_10680,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10676,c_2407])).

cnf(c_10683,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10680,c_586])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_589,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_580,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3557,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_580])).

cnf(c_10695,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_10683,c_3557])).

cnf(c_21126,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_5213,c_10695])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_584,plain,
    ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3989,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_584])).

cnf(c_5247,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_586,c_3989])).

cnf(c_5249,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_5247,c_1879])).

cnf(c_21138,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_10695,c_5249])).

cnf(c_5,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1234,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_934,c_5])).

cnf(c_4,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1231,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_2198,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1231,c_934])).

cnf(c_2206,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1234,c_2198])).

cnf(c_2726,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_2206,c_2407])).

cnf(c_2727,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_2726,c_2407])).

cnf(c_9740,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_2727,c_5213])).

cnf(c_21140,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_21138,c_9740])).

cnf(c_2731,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_2588])).

cnf(c_5214,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_2731,c_5206])).

cnf(c_14083,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_9740,c_5214])).

cnf(c_15596,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_14083,c_11])).

cnf(c_21158,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_21140,c_15596])).

cnf(c_21244,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X1,k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(light_normalisation,[status(thm)],[c_21126,c_21158])).

cnf(c_21161,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_21140,c_9740])).

cnf(c_21176,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_21161,c_21140])).

cnf(c_21160,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_21140,c_14083])).

cnf(c_21181,plain,
    ( k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_21158,c_21160])).

cnf(c_21128,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_5214,c_10695])).

cnf(c_21232,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X0,k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(light_normalisation,[status(thm)],[c_21128,c_21158])).

cnf(c_21233,plain,
    ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_21232,c_21158,c_21181])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_578,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_832,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_586,c_578])).

cnf(c_833,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_832,c_11])).

cnf(c_2413,plain,
    ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1879,c_833])).

cnf(c_8662,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_2413,c_5249])).

cnf(c_8696,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_8662,c_1879])).

cnf(c_21235,plain,
    ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_21233,c_8696])).

cnf(c_21245,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_21244,c_21158,c_21176,c_21181,c_21235])).

cnf(c_20,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1237,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_934,c_20])).

cnf(c_1373,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1370,c_1237])).

cnf(c_2591,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_2407,c_1373])).

cnf(c_2730,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_2727,c_2591])).

cnf(c_21150,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_21140,c_2730])).

cnf(c_21247,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_21245,c_21150])).

cnf(c_21249,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_21247])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:00:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 6.67/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.67/1.47  
% 6.67/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.67/1.47  
% 6.67/1.47  ------  iProver source info
% 6.67/1.47  
% 6.67/1.47  git: date: 2020-06-30 10:37:57 +0100
% 6.67/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.67/1.47  git: non_committed_changes: false
% 6.67/1.47  git: last_make_outside_of_git: false
% 6.67/1.47  
% 6.67/1.47  ------ 
% 6.67/1.47  
% 6.67/1.47  ------ Input Options
% 6.67/1.47  
% 6.67/1.47  --out_options                           all
% 6.67/1.47  --tptp_safe_out                         true
% 6.67/1.47  --problem_path                          ""
% 6.67/1.47  --include_path                          ""
% 6.67/1.47  --clausifier                            res/vclausify_rel
% 6.67/1.47  --clausifier_options                    --mode clausify
% 6.67/1.47  --stdin                                 false
% 6.67/1.47  --stats_out                             all
% 6.67/1.47  
% 6.67/1.47  ------ General Options
% 6.67/1.47  
% 6.67/1.47  --fof                                   false
% 6.67/1.47  --time_out_real                         305.
% 6.67/1.47  --time_out_virtual                      -1.
% 6.67/1.47  --symbol_type_check                     false
% 6.67/1.47  --clausify_out                          false
% 6.67/1.47  --sig_cnt_out                           false
% 6.67/1.47  --trig_cnt_out                          false
% 6.67/1.47  --trig_cnt_out_tolerance                1.
% 6.67/1.47  --trig_cnt_out_sk_spl                   false
% 6.67/1.47  --abstr_cl_out                          false
% 6.67/1.47  
% 6.67/1.47  ------ Global Options
% 6.67/1.47  
% 6.67/1.47  --schedule                              default
% 6.67/1.47  --add_important_lit                     false
% 6.67/1.47  --prop_solver_per_cl                    1000
% 6.67/1.47  --min_unsat_core                        false
% 6.67/1.47  --soft_assumptions                      false
% 6.67/1.47  --soft_lemma_size                       3
% 6.67/1.47  --prop_impl_unit_size                   0
% 6.67/1.47  --prop_impl_unit                        []
% 6.67/1.47  --share_sel_clauses                     true
% 6.67/1.47  --reset_solvers                         false
% 6.67/1.47  --bc_imp_inh                            [conj_cone]
% 6.67/1.47  --conj_cone_tolerance                   3.
% 6.67/1.47  --extra_neg_conj                        none
% 6.67/1.47  --large_theory_mode                     true
% 6.67/1.47  --prolific_symb_bound                   200
% 6.67/1.47  --lt_threshold                          2000
% 6.67/1.47  --clause_weak_htbl                      true
% 6.67/1.47  --gc_record_bc_elim                     false
% 6.67/1.47  
% 6.67/1.47  ------ Preprocessing Options
% 6.67/1.47  
% 6.67/1.47  --preprocessing_flag                    true
% 6.67/1.47  --time_out_prep_mult                    0.1
% 6.67/1.47  --splitting_mode                        input
% 6.67/1.47  --splitting_grd                         true
% 6.67/1.47  --splitting_cvd                         false
% 6.67/1.47  --splitting_cvd_svl                     false
% 6.67/1.47  --splitting_nvd                         32
% 6.67/1.47  --sub_typing                            true
% 6.67/1.47  --prep_gs_sim                           true
% 6.67/1.47  --prep_unflatten                        true
% 6.67/1.47  --prep_res_sim                          true
% 6.67/1.47  --prep_upred                            true
% 6.67/1.47  --prep_sem_filter                       exhaustive
% 6.67/1.47  --prep_sem_filter_out                   false
% 6.67/1.47  --pred_elim                             true
% 6.67/1.47  --res_sim_input                         true
% 6.67/1.47  --eq_ax_congr_red                       true
% 6.67/1.47  --pure_diseq_elim                       true
% 6.67/1.47  --brand_transform                       false
% 6.67/1.47  --non_eq_to_eq                          false
% 6.67/1.47  --prep_def_merge                        true
% 6.67/1.47  --prep_def_merge_prop_impl              false
% 6.67/1.47  --prep_def_merge_mbd                    true
% 6.67/1.47  --prep_def_merge_tr_red                 false
% 6.67/1.47  --prep_def_merge_tr_cl                  false
% 6.67/1.47  --smt_preprocessing                     true
% 6.67/1.47  --smt_ac_axioms                         fast
% 6.67/1.47  --preprocessed_out                      false
% 6.67/1.47  --preprocessed_stats                    false
% 6.67/1.47  
% 6.67/1.47  ------ Abstraction refinement Options
% 6.67/1.47  
% 6.67/1.47  --abstr_ref                             []
% 6.67/1.47  --abstr_ref_prep                        false
% 6.67/1.47  --abstr_ref_until_sat                   false
% 6.67/1.47  --abstr_ref_sig_restrict                funpre
% 6.67/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 6.67/1.47  --abstr_ref_under                       []
% 6.67/1.47  
% 6.67/1.47  ------ SAT Options
% 6.67/1.47  
% 6.67/1.47  --sat_mode                              false
% 6.67/1.47  --sat_fm_restart_options                ""
% 6.67/1.47  --sat_gr_def                            false
% 6.67/1.47  --sat_epr_types                         true
% 6.67/1.47  --sat_non_cyclic_types                  false
% 6.67/1.47  --sat_finite_models                     false
% 6.67/1.47  --sat_fm_lemmas                         false
% 6.67/1.47  --sat_fm_prep                           false
% 6.67/1.47  --sat_fm_uc_incr                        true
% 6.67/1.47  --sat_out_model                         small
% 6.67/1.47  --sat_out_clauses                       false
% 6.67/1.47  
% 6.67/1.47  ------ QBF Options
% 6.67/1.47  
% 6.67/1.47  --qbf_mode                              false
% 6.67/1.47  --qbf_elim_univ                         false
% 6.67/1.47  --qbf_dom_inst                          none
% 6.67/1.47  --qbf_dom_pre_inst                      false
% 6.67/1.47  --qbf_sk_in                             false
% 6.67/1.47  --qbf_pred_elim                         true
% 6.67/1.47  --qbf_split                             512
% 6.67/1.47  
% 6.67/1.47  ------ BMC1 Options
% 6.67/1.47  
% 6.67/1.47  --bmc1_incremental                      false
% 6.67/1.47  --bmc1_axioms                           reachable_all
% 6.67/1.47  --bmc1_min_bound                        0
% 6.67/1.47  --bmc1_max_bound                        -1
% 6.67/1.47  --bmc1_max_bound_default                -1
% 6.67/1.47  --bmc1_symbol_reachability              true
% 6.67/1.47  --bmc1_property_lemmas                  false
% 6.67/1.47  --bmc1_k_induction                      false
% 6.67/1.47  --bmc1_non_equiv_states                 false
% 6.67/1.47  --bmc1_deadlock                         false
% 6.67/1.47  --bmc1_ucm                              false
% 6.67/1.47  --bmc1_add_unsat_core                   none
% 6.67/1.47  --bmc1_unsat_core_children              false
% 6.67/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 6.67/1.47  --bmc1_out_stat                         full
% 6.67/1.47  --bmc1_ground_init                      false
% 6.67/1.47  --bmc1_pre_inst_next_state              false
% 6.67/1.47  --bmc1_pre_inst_state                   false
% 6.67/1.47  --bmc1_pre_inst_reach_state             false
% 6.67/1.47  --bmc1_out_unsat_core                   false
% 6.67/1.47  --bmc1_aig_witness_out                  false
% 6.67/1.47  --bmc1_verbose                          false
% 6.67/1.47  --bmc1_dump_clauses_tptp                false
% 6.67/1.47  --bmc1_dump_unsat_core_tptp             false
% 6.67/1.47  --bmc1_dump_file                        -
% 6.67/1.47  --bmc1_ucm_expand_uc_limit              128
% 6.67/1.47  --bmc1_ucm_n_expand_iterations          6
% 6.67/1.47  --bmc1_ucm_extend_mode                  1
% 6.67/1.47  --bmc1_ucm_init_mode                    2
% 6.67/1.47  --bmc1_ucm_cone_mode                    none
% 6.67/1.47  --bmc1_ucm_reduced_relation_type        0
% 6.67/1.47  --bmc1_ucm_relax_model                  4
% 6.67/1.47  --bmc1_ucm_full_tr_after_sat            true
% 6.67/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 6.67/1.47  --bmc1_ucm_layered_model                none
% 6.67/1.47  --bmc1_ucm_max_lemma_size               10
% 6.67/1.47  
% 6.67/1.47  ------ AIG Options
% 6.67/1.47  
% 6.67/1.47  --aig_mode                              false
% 6.67/1.47  
% 6.67/1.47  ------ Instantiation Options
% 6.67/1.47  
% 6.67/1.47  --instantiation_flag                    true
% 6.67/1.47  --inst_sos_flag                         false
% 6.67/1.47  --inst_sos_phase                        true
% 6.67/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.67/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.67/1.47  --inst_lit_sel_side                     num_symb
% 6.67/1.47  --inst_solver_per_active                1400
% 6.67/1.47  --inst_solver_calls_frac                1.
% 6.67/1.47  --inst_passive_queue_type               priority_queues
% 6.67/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.67/1.47  --inst_passive_queues_freq              [25;2]
% 6.67/1.47  --inst_dismatching                      true
% 6.67/1.47  --inst_eager_unprocessed_to_passive     true
% 6.67/1.47  --inst_prop_sim_given                   true
% 6.67/1.47  --inst_prop_sim_new                     false
% 6.67/1.47  --inst_subs_new                         false
% 6.67/1.48  --inst_eq_res_simp                      false
% 6.67/1.48  --inst_subs_given                       false
% 6.67/1.48  --inst_orphan_elimination               true
% 6.67/1.48  --inst_learning_loop_flag               true
% 6.67/1.48  --inst_learning_start                   3000
% 6.67/1.48  --inst_learning_factor                  2
% 6.67/1.48  --inst_start_prop_sim_after_learn       3
% 6.67/1.48  --inst_sel_renew                        solver
% 6.67/1.48  --inst_lit_activity_flag                true
% 6.67/1.48  --inst_restr_to_given                   false
% 6.67/1.48  --inst_activity_threshold               500
% 6.67/1.48  --inst_out_proof                        true
% 6.67/1.48  
% 6.67/1.48  ------ Resolution Options
% 6.67/1.48  
% 6.67/1.48  --resolution_flag                       true
% 6.67/1.48  --res_lit_sel                           adaptive
% 6.67/1.48  --res_lit_sel_side                      none
% 6.67/1.48  --res_ordering                          kbo
% 6.67/1.48  --res_to_prop_solver                    active
% 6.67/1.48  --res_prop_simpl_new                    false
% 6.67/1.48  --res_prop_simpl_given                  true
% 6.67/1.48  --res_passive_queue_type                priority_queues
% 6.67/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.67/1.48  --res_passive_queues_freq               [15;5]
% 6.67/1.48  --res_forward_subs                      full
% 6.67/1.48  --res_backward_subs                     full
% 6.67/1.48  --res_forward_subs_resolution           true
% 6.67/1.48  --res_backward_subs_resolution          true
% 6.67/1.48  --res_orphan_elimination                true
% 6.67/1.48  --res_time_limit                        2.
% 6.67/1.48  --res_out_proof                         true
% 6.67/1.48  
% 6.67/1.48  ------ Superposition Options
% 6.67/1.48  
% 6.67/1.48  --superposition_flag                    true
% 6.67/1.48  --sup_passive_queue_type                priority_queues
% 6.67/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.67/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.67/1.48  --demod_completeness_check              fast
% 6.67/1.48  --demod_use_ground                      true
% 6.67/1.48  --sup_to_prop_solver                    passive
% 6.67/1.48  --sup_prop_simpl_new                    true
% 6.67/1.48  --sup_prop_simpl_given                  true
% 6.67/1.48  --sup_fun_splitting                     false
% 6.67/1.48  --sup_smt_interval                      50000
% 6.67/1.48  
% 6.67/1.48  ------ Superposition Simplification Setup
% 6.67/1.48  
% 6.67/1.48  --sup_indices_passive                   []
% 6.67/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.67/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.48  --sup_full_bw                           [BwDemod]
% 6.67/1.48  --sup_immed_triv                        [TrivRules]
% 6.67/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.67/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.48  --sup_immed_bw_main                     []
% 6.67/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.67/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.48  
% 6.67/1.48  ------ Combination Options
% 6.67/1.48  
% 6.67/1.48  --comb_res_mult                         3
% 6.67/1.48  --comb_sup_mult                         2
% 6.67/1.48  --comb_inst_mult                        10
% 6.67/1.48  
% 6.67/1.48  ------ Debug Options
% 6.67/1.48  
% 6.67/1.48  --dbg_backtrace                         false
% 6.67/1.48  --dbg_dump_prop_clauses                 false
% 6.67/1.48  --dbg_dump_prop_clauses_file            -
% 6.67/1.48  --dbg_out_stat                          false
% 6.67/1.48  ------ Parsing...
% 6.67/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.67/1.48  
% 6.67/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.67/1.48  
% 6.67/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.67/1.48  
% 6.67/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.67/1.48  ------ Proving...
% 6.67/1.48  ------ Problem Properties 
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  clauses                                 20
% 6.67/1.48  conjectures                             1
% 6.67/1.48  EPR                                     2
% 6.67/1.48  Horn                                    20
% 6.67/1.48  unary                                   8
% 6.67/1.48  binary                                  6
% 6.67/1.48  lits                                    39
% 6.67/1.48  lits eq                                 14
% 6.67/1.48  fd_pure                                 0
% 6.67/1.48  fd_pseudo                               0
% 6.67/1.48  fd_cond                                 0
% 6.67/1.48  fd_pseudo_cond                          1
% 6.67/1.48  AC symbols                              0
% 6.67/1.48  
% 6.67/1.48  ------ Schedule dynamic 5 is on 
% 6.67/1.48  
% 6.67/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  ------ 
% 6.67/1.48  Current options:
% 6.67/1.48  ------ 
% 6.67/1.48  
% 6.67/1.48  ------ Input Options
% 6.67/1.48  
% 6.67/1.48  --out_options                           all
% 6.67/1.48  --tptp_safe_out                         true
% 6.67/1.48  --problem_path                          ""
% 6.67/1.48  --include_path                          ""
% 6.67/1.48  --clausifier                            res/vclausify_rel
% 6.67/1.48  --clausifier_options                    --mode clausify
% 6.67/1.48  --stdin                                 false
% 6.67/1.48  --stats_out                             all
% 6.67/1.48  
% 6.67/1.48  ------ General Options
% 6.67/1.48  
% 6.67/1.48  --fof                                   false
% 6.67/1.48  --time_out_real                         305.
% 6.67/1.48  --time_out_virtual                      -1.
% 6.67/1.48  --symbol_type_check                     false
% 6.67/1.48  --clausify_out                          false
% 6.67/1.48  --sig_cnt_out                           false
% 6.67/1.48  --trig_cnt_out                          false
% 6.67/1.48  --trig_cnt_out_tolerance                1.
% 6.67/1.48  --trig_cnt_out_sk_spl                   false
% 6.67/1.48  --abstr_cl_out                          false
% 6.67/1.48  
% 6.67/1.48  ------ Global Options
% 6.67/1.48  
% 6.67/1.48  --schedule                              default
% 6.67/1.48  --add_important_lit                     false
% 6.67/1.48  --prop_solver_per_cl                    1000
% 6.67/1.48  --min_unsat_core                        false
% 6.67/1.48  --soft_assumptions                      false
% 6.67/1.48  --soft_lemma_size                       3
% 6.67/1.48  --prop_impl_unit_size                   0
% 6.67/1.48  --prop_impl_unit                        []
% 6.67/1.48  --share_sel_clauses                     true
% 6.67/1.48  --reset_solvers                         false
% 6.67/1.48  --bc_imp_inh                            [conj_cone]
% 6.67/1.48  --conj_cone_tolerance                   3.
% 6.67/1.48  --extra_neg_conj                        none
% 6.67/1.48  --large_theory_mode                     true
% 6.67/1.48  --prolific_symb_bound                   200
% 6.67/1.48  --lt_threshold                          2000
% 6.67/1.48  --clause_weak_htbl                      true
% 6.67/1.48  --gc_record_bc_elim                     false
% 6.67/1.48  
% 6.67/1.48  ------ Preprocessing Options
% 6.67/1.48  
% 6.67/1.48  --preprocessing_flag                    true
% 6.67/1.48  --time_out_prep_mult                    0.1
% 6.67/1.48  --splitting_mode                        input
% 6.67/1.48  --splitting_grd                         true
% 6.67/1.48  --splitting_cvd                         false
% 6.67/1.48  --splitting_cvd_svl                     false
% 6.67/1.48  --splitting_nvd                         32
% 6.67/1.48  --sub_typing                            true
% 6.67/1.48  --prep_gs_sim                           true
% 6.67/1.48  --prep_unflatten                        true
% 6.67/1.48  --prep_res_sim                          true
% 6.67/1.48  --prep_upred                            true
% 6.67/1.48  --prep_sem_filter                       exhaustive
% 6.67/1.48  --prep_sem_filter_out                   false
% 6.67/1.48  --pred_elim                             true
% 6.67/1.48  --res_sim_input                         true
% 6.67/1.48  --eq_ax_congr_red                       true
% 6.67/1.48  --pure_diseq_elim                       true
% 6.67/1.48  --brand_transform                       false
% 6.67/1.48  --non_eq_to_eq                          false
% 6.67/1.48  --prep_def_merge                        true
% 6.67/1.48  --prep_def_merge_prop_impl              false
% 6.67/1.48  --prep_def_merge_mbd                    true
% 6.67/1.48  --prep_def_merge_tr_red                 false
% 6.67/1.48  --prep_def_merge_tr_cl                  false
% 6.67/1.48  --smt_preprocessing                     true
% 6.67/1.48  --smt_ac_axioms                         fast
% 6.67/1.48  --preprocessed_out                      false
% 6.67/1.48  --preprocessed_stats                    false
% 6.67/1.48  
% 6.67/1.48  ------ Abstraction refinement Options
% 6.67/1.48  
% 6.67/1.48  --abstr_ref                             []
% 6.67/1.48  --abstr_ref_prep                        false
% 6.67/1.48  --abstr_ref_until_sat                   false
% 6.67/1.48  --abstr_ref_sig_restrict                funpre
% 6.67/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.67/1.48  --abstr_ref_under                       []
% 6.67/1.48  
% 6.67/1.48  ------ SAT Options
% 6.67/1.48  
% 6.67/1.48  --sat_mode                              false
% 6.67/1.48  --sat_fm_restart_options                ""
% 6.67/1.48  --sat_gr_def                            false
% 6.67/1.48  --sat_epr_types                         true
% 6.67/1.48  --sat_non_cyclic_types                  false
% 6.67/1.48  --sat_finite_models                     false
% 6.67/1.48  --sat_fm_lemmas                         false
% 6.67/1.48  --sat_fm_prep                           false
% 6.67/1.48  --sat_fm_uc_incr                        true
% 6.67/1.48  --sat_out_model                         small
% 6.67/1.48  --sat_out_clauses                       false
% 6.67/1.48  
% 6.67/1.48  ------ QBF Options
% 6.67/1.48  
% 6.67/1.48  --qbf_mode                              false
% 6.67/1.48  --qbf_elim_univ                         false
% 6.67/1.48  --qbf_dom_inst                          none
% 6.67/1.48  --qbf_dom_pre_inst                      false
% 6.67/1.48  --qbf_sk_in                             false
% 6.67/1.48  --qbf_pred_elim                         true
% 6.67/1.48  --qbf_split                             512
% 6.67/1.48  
% 6.67/1.48  ------ BMC1 Options
% 6.67/1.48  
% 6.67/1.48  --bmc1_incremental                      false
% 6.67/1.48  --bmc1_axioms                           reachable_all
% 6.67/1.48  --bmc1_min_bound                        0
% 6.67/1.48  --bmc1_max_bound                        -1
% 6.67/1.48  --bmc1_max_bound_default                -1
% 6.67/1.48  --bmc1_symbol_reachability              true
% 6.67/1.48  --bmc1_property_lemmas                  false
% 6.67/1.48  --bmc1_k_induction                      false
% 6.67/1.48  --bmc1_non_equiv_states                 false
% 6.67/1.48  --bmc1_deadlock                         false
% 6.67/1.48  --bmc1_ucm                              false
% 6.67/1.48  --bmc1_add_unsat_core                   none
% 6.67/1.48  --bmc1_unsat_core_children              false
% 6.67/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.67/1.48  --bmc1_out_stat                         full
% 6.67/1.48  --bmc1_ground_init                      false
% 6.67/1.48  --bmc1_pre_inst_next_state              false
% 6.67/1.48  --bmc1_pre_inst_state                   false
% 6.67/1.48  --bmc1_pre_inst_reach_state             false
% 6.67/1.48  --bmc1_out_unsat_core                   false
% 6.67/1.48  --bmc1_aig_witness_out                  false
% 6.67/1.48  --bmc1_verbose                          false
% 6.67/1.48  --bmc1_dump_clauses_tptp                false
% 6.67/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.67/1.48  --bmc1_dump_file                        -
% 6.67/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.67/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.67/1.48  --bmc1_ucm_extend_mode                  1
% 6.67/1.48  --bmc1_ucm_init_mode                    2
% 6.67/1.48  --bmc1_ucm_cone_mode                    none
% 6.67/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.67/1.48  --bmc1_ucm_relax_model                  4
% 6.67/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.67/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.67/1.48  --bmc1_ucm_layered_model                none
% 6.67/1.48  --bmc1_ucm_max_lemma_size               10
% 6.67/1.48  
% 6.67/1.48  ------ AIG Options
% 6.67/1.48  
% 6.67/1.48  --aig_mode                              false
% 6.67/1.48  
% 6.67/1.48  ------ Instantiation Options
% 6.67/1.48  
% 6.67/1.48  --instantiation_flag                    true
% 6.67/1.48  --inst_sos_flag                         false
% 6.67/1.48  --inst_sos_phase                        true
% 6.67/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.67/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.67/1.48  --inst_lit_sel_side                     none
% 6.67/1.48  --inst_solver_per_active                1400
% 6.67/1.48  --inst_solver_calls_frac                1.
% 6.67/1.48  --inst_passive_queue_type               priority_queues
% 6.67/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.67/1.48  --inst_passive_queues_freq              [25;2]
% 6.67/1.48  --inst_dismatching                      true
% 6.67/1.48  --inst_eager_unprocessed_to_passive     true
% 6.67/1.48  --inst_prop_sim_given                   true
% 6.67/1.48  --inst_prop_sim_new                     false
% 6.67/1.48  --inst_subs_new                         false
% 6.67/1.48  --inst_eq_res_simp                      false
% 6.67/1.48  --inst_subs_given                       false
% 6.67/1.48  --inst_orphan_elimination               true
% 6.67/1.48  --inst_learning_loop_flag               true
% 6.67/1.48  --inst_learning_start                   3000
% 6.67/1.48  --inst_learning_factor                  2
% 6.67/1.48  --inst_start_prop_sim_after_learn       3
% 6.67/1.48  --inst_sel_renew                        solver
% 6.67/1.48  --inst_lit_activity_flag                true
% 6.67/1.48  --inst_restr_to_given                   false
% 6.67/1.48  --inst_activity_threshold               500
% 6.67/1.48  --inst_out_proof                        true
% 6.67/1.48  
% 6.67/1.48  ------ Resolution Options
% 6.67/1.48  
% 6.67/1.48  --resolution_flag                       false
% 6.67/1.48  --res_lit_sel                           adaptive
% 6.67/1.48  --res_lit_sel_side                      none
% 6.67/1.48  --res_ordering                          kbo
% 6.67/1.48  --res_to_prop_solver                    active
% 6.67/1.48  --res_prop_simpl_new                    false
% 6.67/1.48  --res_prop_simpl_given                  true
% 6.67/1.48  --res_passive_queue_type                priority_queues
% 6.67/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.67/1.48  --res_passive_queues_freq               [15;5]
% 6.67/1.48  --res_forward_subs                      full
% 6.67/1.48  --res_backward_subs                     full
% 6.67/1.48  --res_forward_subs_resolution           true
% 6.67/1.48  --res_backward_subs_resolution          true
% 6.67/1.48  --res_orphan_elimination                true
% 6.67/1.48  --res_time_limit                        2.
% 6.67/1.48  --res_out_proof                         true
% 6.67/1.48  
% 6.67/1.48  ------ Superposition Options
% 6.67/1.48  
% 6.67/1.48  --superposition_flag                    true
% 6.67/1.48  --sup_passive_queue_type                priority_queues
% 6.67/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.67/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.67/1.48  --demod_completeness_check              fast
% 6.67/1.48  --demod_use_ground                      true
% 6.67/1.48  --sup_to_prop_solver                    passive
% 6.67/1.48  --sup_prop_simpl_new                    true
% 6.67/1.48  --sup_prop_simpl_given                  true
% 6.67/1.48  --sup_fun_splitting                     false
% 6.67/1.48  --sup_smt_interval                      50000
% 6.67/1.48  
% 6.67/1.48  ------ Superposition Simplification Setup
% 6.67/1.48  
% 6.67/1.48  --sup_indices_passive                   []
% 6.67/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.67/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.48  --sup_full_bw                           [BwDemod]
% 6.67/1.48  --sup_immed_triv                        [TrivRules]
% 6.67/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.67/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.48  --sup_immed_bw_main                     []
% 6.67/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.67/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.48  
% 6.67/1.48  ------ Combination Options
% 6.67/1.48  
% 6.67/1.48  --comb_res_mult                         3
% 6.67/1.48  --comb_sup_mult                         2
% 6.67/1.48  --comb_inst_mult                        10
% 6.67/1.48  
% 6.67/1.48  ------ Debug Options
% 6.67/1.48  
% 6.67/1.48  --dbg_backtrace                         false
% 6.67/1.48  --dbg_dump_prop_clauses                 false
% 6.67/1.48  --dbg_dump_prop_clauses_file            -
% 6.67/1.48  --dbg_out_stat                          false
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  ------ Proving...
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  % SZS status Theorem for theBenchmark.p
% 6.67/1.48  
% 6.67/1.48   Resolution empty clause
% 6.67/1.48  
% 6.67/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.67/1.48  
% 6.67/1.48  fof(f13,axiom,(
% 6.67/1.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f58,plain,(
% 6.67/1.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.67/1.48    inference(cnf_transformation,[],[f13])).
% 6.67/1.48  
% 6.67/1.48  fof(f14,axiom,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f28,plain,(
% 6.67/1.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(ennf_transformation,[],[f14])).
% 6.67/1.48  
% 6.67/1.48  fof(f59,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f28])).
% 6.67/1.48  
% 6.67/1.48  fof(f23,axiom,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f38,plain,(
% 6.67/1.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(ennf_transformation,[],[f23])).
% 6.67/1.48  
% 6.67/1.48  fof(f70,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f38])).
% 6.67/1.48  
% 6.67/1.48  fof(f22,axiom,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f37,plain,(
% 6.67/1.48    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(ennf_transformation,[],[f22])).
% 6.67/1.48  
% 6.67/1.48  fof(f69,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f37])).
% 6.67/1.48  
% 6.67/1.48  fof(f3,axiom,(
% 6.67/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f48,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.67/1.48    inference(cnf_transformation,[],[f3])).
% 6.67/1.48  
% 6.67/1.48  fof(f80,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f69,f48])).
% 6.67/1.48  
% 6.67/1.48  fof(f17,axiom,(
% 6.67/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f62,plain,(
% 6.67/1.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.67/1.48    inference(cnf_transformation,[],[f17])).
% 6.67/1.48  
% 6.67/1.48  fof(f2,axiom,(
% 6.67/1.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f47,plain,(
% 6.67/1.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f2])).
% 6.67/1.48  
% 6.67/1.48  fof(f77,plain,(
% 6.67/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f47,f48])).
% 6.67/1.48  
% 6.67/1.48  fof(f63,plain,(
% 6.67/1.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 6.67/1.48    inference(cnf_transformation,[],[f17])).
% 6.67/1.48  
% 6.67/1.48  fof(f20,axiom,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f34,plain,(
% 6.67/1.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(ennf_transformation,[],[f20])).
% 6.67/1.48  
% 6.67/1.48  fof(f35,plain,(
% 6.67/1.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(flattening,[],[f34])).
% 6.67/1.48  
% 6.67/1.48  fof(f67,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f35])).
% 6.67/1.48  
% 6.67/1.48  fof(f12,axiom,(
% 6.67/1.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f26,plain,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 6.67/1.48    inference(ennf_transformation,[],[f12])).
% 6.67/1.48  
% 6.67/1.48  fof(f27,plain,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 6.67/1.48    inference(flattening,[],[f26])).
% 6.67/1.48  
% 6.67/1.48  fof(f57,plain,(
% 6.67/1.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f27])).
% 6.67/1.48  
% 6.67/1.48  fof(f1,axiom,(
% 6.67/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f40,plain,(
% 6.67/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.67/1.48    inference(nnf_transformation,[],[f1])).
% 6.67/1.48  
% 6.67/1.48  fof(f41,plain,(
% 6.67/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.67/1.48    inference(flattening,[],[f40])).
% 6.67/1.48  
% 6.67/1.48  fof(f45,plain,(
% 6.67/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.67/1.48    inference(cnf_transformation,[],[f41])).
% 6.67/1.48  
% 6.67/1.48  fof(f82,plain,(
% 6.67/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.67/1.48    inference(equality_resolution,[],[f45])).
% 6.67/1.48  
% 6.67/1.48  fof(f19,axiom,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f32,plain,(
% 6.67/1.48    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(ennf_transformation,[],[f19])).
% 6.67/1.48  
% 6.67/1.48  fof(f33,plain,(
% 6.67/1.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(flattening,[],[f32])).
% 6.67/1.48  
% 6.67/1.48  fof(f66,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f33])).
% 6.67/1.48  
% 6.67/1.48  fof(f15,axiom,(
% 6.67/1.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f29,plain,(
% 6.67/1.48    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 6.67/1.48    inference(ennf_transformation,[],[f15])).
% 6.67/1.48  
% 6.67/1.48  fof(f60,plain,(
% 6.67/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f29])).
% 6.67/1.48  
% 6.67/1.48  fof(f11,axiom,(
% 6.67/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f56,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.67/1.48    inference(cnf_transformation,[],[f11])).
% 6.67/1.48  
% 6.67/1.48  fof(f5,axiom,(
% 6.67/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f50,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f5])).
% 6.67/1.48  
% 6.67/1.48  fof(f6,axiom,(
% 6.67/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f51,plain,(
% 6.67/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f6])).
% 6.67/1.48  
% 6.67/1.48  fof(f7,axiom,(
% 6.67/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f52,plain,(
% 6.67/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f7])).
% 6.67/1.48  
% 6.67/1.48  fof(f8,axiom,(
% 6.67/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f53,plain,(
% 6.67/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f8])).
% 6.67/1.48  
% 6.67/1.48  fof(f9,axiom,(
% 6.67/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f54,plain,(
% 6.67/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f9])).
% 6.67/1.48  
% 6.67/1.48  fof(f10,axiom,(
% 6.67/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f55,plain,(
% 6.67/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f10])).
% 6.67/1.48  
% 6.67/1.48  fof(f72,plain,(
% 6.67/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f54,f55])).
% 6.67/1.48  
% 6.67/1.48  fof(f73,plain,(
% 6.67/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f53,f72])).
% 6.67/1.48  
% 6.67/1.48  fof(f74,plain,(
% 6.67/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f52,f73])).
% 6.67/1.48  
% 6.67/1.48  fof(f75,plain,(
% 6.67/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f51,f74])).
% 6.67/1.48  
% 6.67/1.48  fof(f76,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f50,f75])).
% 6.67/1.48  
% 6.67/1.48  fof(f79,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.67/1.48    inference(definition_unfolding,[],[f56,f48,f76])).
% 6.67/1.48  
% 6.67/1.48  fof(f4,axiom,(
% 6.67/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f49,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f4])).
% 6.67/1.48  
% 6.67/1.48  fof(f78,plain,(
% 6.67/1.48    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 6.67/1.48    inference(definition_unfolding,[],[f49,f76,f76])).
% 6.67/1.48  
% 6.67/1.48  fof(f21,axiom,(
% 6.67/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f36,plain,(
% 6.67/1.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 6.67/1.48    inference(ennf_transformation,[],[f21])).
% 6.67/1.48  
% 6.67/1.48  fof(f68,plain,(
% 6.67/1.48    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 6.67/1.48    inference(cnf_transformation,[],[f36])).
% 6.67/1.48  
% 6.67/1.48  fof(f24,conjecture,(
% 6.67/1.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 6.67/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.48  
% 6.67/1.48  fof(f25,negated_conjecture,(
% 6.67/1.48    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 6.67/1.48    inference(negated_conjecture,[],[f24])).
% 6.67/1.48  
% 6.67/1.48  fof(f39,plain,(
% 6.67/1.48    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 6.67/1.48    inference(ennf_transformation,[],[f25])).
% 6.67/1.48  
% 6.67/1.48  fof(f42,plain,(
% 6.67/1.48    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 6.67/1.48    introduced(choice_axiom,[])).
% 6.67/1.48  
% 6.67/1.48  fof(f43,plain,(
% 6.67/1.48    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 6.67/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f42])).
% 6.67/1.48  
% 6.67/1.48  fof(f71,plain,(
% 6.67/1.48    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 6.67/1.48    inference(cnf_transformation,[],[f43])).
% 6.67/1.48  
% 6.67/1.48  fof(f81,plain,(
% 6.67/1.48    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 6.67/1.48    inference(definition_unfolding,[],[f71,f48])).
% 6.67/1.48  
% 6.67/1.48  cnf(c_7,plain,
% 6.67/1.48      ( v1_relat_1(k6_relat_1(X0)) ),
% 6.67/1.48      inference(cnf_transformation,[],[f58]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_586,plain,
% 6.67/1.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_8,plain,
% 6.67/1.48      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 6.67/1.48      inference(cnf_transformation,[],[f59]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_585,plain,
% 6.67/1.48      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 6.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1879,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_586,c_585]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_19,plain,
% 6.67/1.48      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 6.67/1.48      inference(cnf_transformation,[],[f70]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_576,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 6.67/1.48      | v1_relat_1(X1) != iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1370,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_586,c_576]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2407,plain,
% 6.67/1.48      ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_1879,c_1370]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_18,plain,
% 6.67/1.48      ( ~ v1_relat_1(X0)
% 6.67/1.48      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 6.67/1.48      inference(cnf_transformation,[],[f80]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_577,plain,
% 6.67/1.48      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 6.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_933,plain,
% 6.67/1.48      ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_586,c_577]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_12,plain,
% 6.67/1.48      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 6.67/1.48      inference(cnf_transformation,[],[f62]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_934,plain,
% 6.67/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.67/1.48      inference(light_normalisation,[status(thm)],[c_933,c_12]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_3,plain,
% 6.67/1.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 6.67/1.48      inference(cnf_transformation,[],[f77]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_588,plain,
% 6.67/1.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1235,plain,
% 6.67/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_934,c_588]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2588,plain,
% 6.67/1.48      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_2407,c_1235]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_11,plain,
% 6.67/1.48      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 6.67/1.48      inference(cnf_transformation,[],[f63]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_16,plain,
% 6.67/1.48      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 6.67/1.48      | ~ v1_relat_1(X0)
% 6.67/1.48      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 6.67/1.48      inference(cnf_transformation,[],[f67]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_579,plain,
% 6.67/1.48      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 6.67/1.48      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1886,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 6.67/1.48      | r1_tarski(X0,X1) != iProver_top
% 6.67/1.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_11,c_579]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1890,plain,
% 6.67/1.48      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 6.67/1.48      | r1_tarski(X1,X0) != iProver_top
% 6.67/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_1886,c_1370]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_5202,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 6.67/1.48      | r1_tarski(X1,X0) != iProver_top
% 6.67/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_1890,c_2407]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_5206,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 6.67/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 6.67/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_5202,c_586]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_5213,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_2588,c_5206]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_6,plain,
% 6.67/1.48      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 6.67/1.48      inference(cnf_transformation,[],[f57]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_587,plain,
% 6.67/1.48      ( v1_relat_1(X0) != iProver_top
% 6.67/1.48      | v1_relat_1(X1) != iProver_top
% 6.67/1.48      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2305,plain,
% 6.67/1.48      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 6.67/1.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 6.67/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_1370,c_587]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_53,plain,
% 6.67/1.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_10676,plain,
% 6.67/1.48      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 6.67/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.67/1.48      inference(global_propositional_subsumption,[status(thm)],[c_2305,c_53]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_10680,plain,
% 6.67/1.48      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 6.67/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.67/1.48      inference(light_normalisation,[status(thm)],[c_10676,c_2407]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_10683,plain,
% 6.67/1.48      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
% 6.67/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_10680,c_586]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f82]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_589,plain,
% 6.67/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_15,plain,
% 6.67/1.48      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 6.67/1.48      | ~ v1_relat_1(X0)
% 6.67/1.48      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 6.67/1.48      inference(cnf_transformation,[],[f66]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_580,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 6.67/1.48      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 6.67/1.48      | v1_relat_1(X1) != iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_3557,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 6.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_589,c_580]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_10695,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_10683,c_3557]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21126,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_5213,c_10695]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_9,plain,
% 6.67/1.48      ( ~ v1_relat_1(X0)
% 6.67/1.48      | ~ v1_relat_1(X1)
% 6.67/1.48      | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
% 6.67/1.48      inference(cnf_transformation,[],[f60]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_584,plain,
% 6.67/1.48      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
% 6.67/1.48      | v1_relat_1(X1) != iProver_top
% 6.67/1.48      | v1_relat_1(X2) != iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_3989,plain,
% 6.67/1.48      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
% 6.67/1.48      | v1_relat_1(X2) != iProver_top ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_586,c_584]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_5247,plain,
% 6.67/1.48      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_586,c_3989]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_5249,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_5247,c_1879]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21138,plain,
% 6.67/1.48      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_10695,c_5249]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_5,plain,
% 6.67/1.48      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 6.67/1.48      inference(cnf_transformation,[],[f79]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1234,plain,
% 6.67/1.48      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_934,c_5]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_4,plain,
% 6.67/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 6.67/1.48      inference(cnf_transformation,[],[f78]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1231,plain,
% 6.67/1.48      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2198,plain,
% 6.67/1.48      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_1231,c_934]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2206,plain,
% 6.67/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_1234,c_2198]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2726,plain,
% 6.67/1.48      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 6.67/1.48      inference(light_normalisation,[status(thm)],[c_2206,c_2407]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2727,plain,
% 6.67/1.48      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_2726,c_2407]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_9740,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_2727,c_5213]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21140,plain,
% 6.67/1.48      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21138,c_9740]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2731,plain,
% 6.67/1.48      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_2727,c_2588]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_5214,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_2731,c_5206]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_14083,plain,
% 6.67/1.48      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_9740,c_5214]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_15596,plain,
% 6.67/1.48      ( k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_14083,c_11]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21158,plain,
% 6.67/1.48      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21140,c_15596]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21244,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X1,k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 6.67/1.48      inference(light_normalisation,[status(thm)],[c_21126,c_21158]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21161,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21140,c_9740]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21176,plain,
% 6.67/1.48      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21161,c_21140]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21160,plain,
% 6.67/1.48      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21140,c_14083]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21181,plain,
% 6.67/1.48      ( k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21158,c_21160]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21128,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_5214,c_10695]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21232,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X0,k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 6.67/1.48      inference(light_normalisation,[status(thm)],[c_21128,c_21158]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21233,plain,
% 6.67/1.48      ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X0))) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21232,c_21158,c_21181]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_17,plain,
% 6.67/1.48      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 6.67/1.48      inference(cnf_transformation,[],[f68]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_578,plain,
% 6.67/1.48      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 6.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.67/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_832,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_586,c_578]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_833,plain,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 6.67/1.48      inference(light_normalisation,[status(thm)],[c_832,c_11]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2413,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_1879,c_833]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_8662,plain,
% 6.67/1.48      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 6.67/1.48      inference(superposition,[status(thm)],[c_2413,c_5249]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_8696,plain,
% 6.67/1.48      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_8662,c_1879]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21235,plain,
% 6.67/1.48      ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21233,c_8696]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21245,plain,
% 6.67/1.48      ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.67/1.48      inference(demodulation,
% 6.67/1.48                [status(thm)],
% 6.67/1.48                [c_21244,c_21158,c_21176,c_21181,c_21235]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_20,negated_conjecture,
% 6.67/1.48      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 6.67/1.48      inference(cnf_transformation,[],[f81]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1237,plain,
% 6.67/1.48      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_934,c_20]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_1373,plain,
% 6.67/1.48      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_1370,c_1237]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2591,plain,
% 6.67/1.48      ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_2407,c_1373]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_2730,plain,
% 6.67/1.48      ( k6_relat_1(k1_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_2727,c_2591]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21150,plain,
% 6.67/1.48      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21140,c_2730]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21247,plain,
% 6.67/1.48      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK1,k6_relat_1(sK0)) ),
% 6.67/1.48      inference(demodulation,[status(thm)],[c_21245,c_21150]) ).
% 6.67/1.48  
% 6.67/1.48  cnf(c_21249,plain,
% 6.67/1.48      ( $false ),
% 6.67/1.48      inference(equality_resolution_simp,[status(thm)],[c_21247]) ).
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.67/1.48  
% 6.67/1.48  ------                               Statistics
% 6.67/1.48  
% 6.67/1.48  ------ General
% 6.67/1.48  
% 6.67/1.48  abstr_ref_over_cycles:                  0
% 6.67/1.48  abstr_ref_under_cycles:                 0
% 6.67/1.48  gc_basic_clause_elim:                   0
% 6.67/1.48  forced_gc_time:                         0
% 6.67/1.48  parsing_time:                           0.009
% 6.67/1.48  unif_index_cands_time:                  0.
% 6.67/1.48  unif_index_add_time:                    0.
% 6.67/1.48  orderings_time:                         0.
% 6.67/1.48  out_proof_time:                         0.01
% 6.67/1.48  total_time:                             0.574
% 6.67/1.48  num_of_symbols:                         44
% 6.67/1.48  num_of_terms:                           27770
% 6.67/1.48  
% 6.67/1.48  ------ Preprocessing
% 6.67/1.48  
% 6.67/1.48  num_of_splits:                          0
% 6.67/1.48  num_of_split_atoms:                     0
% 6.67/1.48  num_of_reused_defs:                     0
% 6.67/1.48  num_eq_ax_congr_red:                    36
% 6.67/1.48  num_of_sem_filtered_clauses:            1
% 6.67/1.48  num_of_subtypes:                        0
% 6.67/1.48  monotx_restored_types:                  0
% 6.67/1.48  sat_num_of_epr_types:                   0
% 6.67/1.48  sat_num_of_non_cyclic_types:            0
% 6.67/1.48  sat_guarded_non_collapsed_types:        0
% 6.67/1.48  num_pure_diseq_elim:                    0
% 6.67/1.48  simp_replaced_by:                       0
% 6.67/1.48  res_preprocessed:                       103
% 6.67/1.48  prep_upred:                             0
% 6.67/1.48  prep_unflattend:                        0
% 6.67/1.48  smt_new_axioms:                         0
% 6.67/1.48  pred_elim_cands:                        2
% 6.67/1.48  pred_elim:                              0
% 6.67/1.48  pred_elim_cl:                           0
% 6.67/1.48  pred_elim_cycles:                       2
% 6.67/1.48  merged_defs:                            0
% 6.67/1.48  merged_defs_ncl:                        0
% 6.67/1.48  bin_hyper_res:                          0
% 6.67/1.48  prep_cycles:                            4
% 6.67/1.48  pred_elim_time:                         0.
% 6.67/1.48  splitting_time:                         0.
% 6.67/1.48  sem_filter_time:                        0.
% 6.67/1.48  monotx_time:                            0.
% 6.67/1.48  subtype_inf_time:                       0.
% 6.67/1.48  
% 6.67/1.48  ------ Problem properties
% 6.67/1.48  
% 6.67/1.48  clauses:                                20
% 6.67/1.48  conjectures:                            1
% 6.67/1.48  epr:                                    2
% 6.67/1.48  horn:                                   20
% 6.67/1.48  ground:                                 1
% 6.67/1.48  unary:                                  8
% 6.67/1.48  binary:                                 6
% 6.67/1.48  lits:                                   39
% 6.67/1.48  lits_eq:                                14
% 6.67/1.48  fd_pure:                                0
% 6.67/1.48  fd_pseudo:                              0
% 6.67/1.48  fd_cond:                                0
% 6.67/1.48  fd_pseudo_cond:                         1
% 6.67/1.48  ac_symbols:                             0
% 6.67/1.48  
% 6.67/1.48  ------ Propositional Solver
% 6.67/1.48  
% 6.67/1.48  prop_solver_calls:                      30
% 6.67/1.48  prop_fast_solver_calls:                 642
% 6.67/1.48  smt_solver_calls:                       0
% 6.67/1.48  smt_fast_solver_calls:                  0
% 6.67/1.48  prop_num_of_clauses:                    7807
% 6.67/1.48  prop_preprocess_simplified:             16833
% 6.67/1.48  prop_fo_subsumed:                       2
% 6.67/1.48  prop_solver_time:                       0.
% 6.67/1.48  smt_solver_time:                        0.
% 6.67/1.48  smt_fast_solver_time:                   0.
% 6.67/1.48  prop_fast_solver_time:                  0.
% 6.67/1.48  prop_unsat_core_time:                   0.
% 6.67/1.48  
% 6.67/1.48  ------ QBF
% 6.67/1.48  
% 6.67/1.48  qbf_q_res:                              0
% 6.67/1.48  qbf_num_tautologies:                    0
% 6.67/1.48  qbf_prep_cycles:                        0
% 6.67/1.48  
% 6.67/1.48  ------ BMC1
% 6.67/1.48  
% 6.67/1.48  bmc1_current_bound:                     -1
% 6.67/1.48  bmc1_last_solved_bound:                 -1
% 6.67/1.48  bmc1_unsat_core_size:                   -1
% 6.67/1.48  bmc1_unsat_core_parents_size:           -1
% 6.67/1.48  bmc1_merge_next_fun:                    0
% 6.67/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.67/1.48  
% 6.67/1.48  ------ Instantiation
% 6.67/1.48  
% 6.67/1.48  inst_num_of_clauses:                    2255
% 6.67/1.48  inst_num_in_passive:                    1563
% 6.67/1.48  inst_num_in_active:                     694
% 6.67/1.48  inst_num_in_unprocessed:                0
% 6.67/1.48  inst_num_of_loops:                      740
% 6.67/1.48  inst_num_of_learning_restarts:          0
% 6.67/1.48  inst_num_moves_active_passive:          45
% 6.67/1.48  inst_lit_activity:                      0
% 6.67/1.48  inst_lit_activity_moves:                1
% 6.67/1.48  inst_num_tautologies:                   0
% 6.67/1.48  inst_num_prop_implied:                  0
% 6.67/1.48  inst_num_existing_simplified:           0
% 6.67/1.48  inst_num_eq_res_simplified:             0
% 6.67/1.48  inst_num_child_elim:                    0
% 6.67/1.48  inst_num_of_dismatching_blockings:      718
% 6.67/1.48  inst_num_of_non_proper_insts:           1777
% 6.67/1.48  inst_num_of_duplicates:                 0
% 6.67/1.48  inst_inst_num_from_inst_to_res:         0
% 6.67/1.48  inst_dismatching_checking_time:         0.
% 6.67/1.48  
% 6.67/1.48  ------ Resolution
% 6.67/1.48  
% 6.67/1.48  res_num_of_clauses:                     0
% 6.67/1.48  res_num_in_passive:                     0
% 6.67/1.48  res_num_in_active:                      0
% 6.67/1.48  res_num_of_loops:                       107
% 6.67/1.48  res_forward_subset_subsumed:            260
% 6.67/1.48  res_backward_subset_subsumed:           6
% 6.67/1.48  res_forward_subsumed:                   0
% 6.67/1.48  res_backward_subsumed:                  0
% 6.67/1.48  res_forward_subsumption_resolution:     0
% 6.67/1.48  res_backward_subsumption_resolution:    0
% 6.67/1.48  res_clause_to_clause_subsumption:       3520
% 6.67/1.48  res_orphan_elimination:                 0
% 6.67/1.48  res_tautology_del:                      192
% 6.67/1.48  res_num_eq_res_simplified:              0
% 6.67/1.48  res_num_sel_changes:                    0
% 6.67/1.48  res_moves_from_active_to_pass:          0
% 6.67/1.48  
% 6.67/1.48  ------ Superposition
% 6.67/1.48  
% 6.67/1.48  sup_time_total:                         0.
% 6.67/1.48  sup_time_generating:                    0.
% 6.67/1.48  sup_time_sim_full:                      0.
% 6.67/1.48  sup_time_sim_immed:                     0.
% 6.67/1.48  
% 6.67/1.48  sup_num_of_clauses:                     624
% 6.67/1.48  sup_num_in_active:                      103
% 6.67/1.48  sup_num_in_passive:                     521
% 6.67/1.48  sup_num_of_loops:                       147
% 6.67/1.48  sup_fw_superposition:                   1472
% 6.67/1.48  sup_bw_superposition:                   1392
% 6.67/1.48  sup_immediate_simplified:               1369
% 6.67/1.48  sup_given_eliminated:                   2
% 6.67/1.48  comparisons_done:                       0
% 6.67/1.48  comparisons_avoided:                    0
% 6.67/1.48  
% 6.67/1.48  ------ Simplifications
% 6.67/1.48  
% 6.67/1.48  
% 6.67/1.48  sim_fw_subset_subsumed:                 25
% 6.67/1.48  sim_bw_subset_subsumed:                 13
% 6.67/1.48  sim_fw_subsumed:                        267
% 6.67/1.48  sim_bw_subsumed:                        1
% 6.67/1.48  sim_fw_subsumption_res:                 5
% 6.67/1.48  sim_bw_subsumption_res:                 0
% 6.67/1.48  sim_tautology_del:                      2
% 6.67/1.48  sim_eq_tautology_del:                   337
% 6.67/1.48  sim_eq_res_simp:                        0
% 6.67/1.48  sim_fw_demodulated:                     674
% 6.67/1.48  sim_bw_demodulated:                     58
% 6.67/1.48  sim_light_normalised:                   855
% 6.67/1.48  sim_joinable_taut:                      0
% 6.67/1.48  sim_joinable_simp:                      0
% 6.67/1.48  sim_ac_normalised:                      0
% 6.67/1.48  sim_smt_subsumption:                    0
% 6.67/1.48  
%------------------------------------------------------------------------------
