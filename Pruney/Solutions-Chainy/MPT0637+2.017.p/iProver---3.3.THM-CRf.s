%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:58 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  157 (5485 expanded)
%              Number of clauses        :   89 (2026 expanded)
%              Number of leaves         :   22 (1314 expanded)
%              Depth                    :   23
%              Number of atoms          :  259 (7594 expanded)
%              Number of equality atoms :  183 (5110 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f70,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f69,f69])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f41])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f41,f69])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f38,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f39])).

fof(f64,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f64,f41])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_423,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_415,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_823,plain,
    ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_423,c_415])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_824,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_823,c_9])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1069,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_824,c_1])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_422,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1721,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_423,c_422])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_414,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_658,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_423,c_414])).

cnf(c_1724,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_1721,c_658])).

cnf(c_2132,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(light_normalisation,[status(thm)],[c_1069,c_1724])).

cnf(c_2136,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_0,c_2132])).

cnf(c_2763,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_2136,c_2132])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_420,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3769,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_420])).

cnf(c_47,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5174,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3769,c_47])).

cnf(c_5175,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5174])).

cnf(c_5182,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_5175])).

cnf(c_5295,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5182,c_47])).

cnf(c_5302,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_5295])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_418,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3638,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_418])).

cnf(c_3657,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3638,c_1721])).

cnf(c_5576,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3657,c_47])).

cnf(c_5577,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5576])).

cnf(c_5586,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_5302,c_5577])).

cnf(c_6512,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_2763,c_5586])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_424,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2771,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_424])).

cnf(c_5432,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2771,c_47])).

cnf(c_5438,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5432,c_423])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_416,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_581,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_423,c_416])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_582,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_581,c_8])).

cnf(c_3768,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_420])).

cnf(c_3802,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3768,c_9])).

cnf(c_3831,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3802,c_47])).

cnf(c_3838,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3831,c_418])).

cnf(c_5448,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5438,c_3838])).

cnf(c_7964,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_6512,c_5448])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_421,plain,
    ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5215,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_423,c_421])).

cnf(c_5247,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_423,c_5215])).

cnf(c_5249,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_5247,c_1721])).

cnf(c_7971,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5448,c_5249])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_417,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1917,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_417])).

cnf(c_1918,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1917,c_1721])).

cnf(c_5075,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1918,c_423])).

cnf(c_5358,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_5302,c_5075])).

cnf(c_5796,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_2763,c_5358])).

cnf(c_7973,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_7971,c_5796])).

cnf(c_5309,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_5295,c_5075])).

cnf(c_5723,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_2763,c_5309])).

cnf(c_7992,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(demodulation,[status(thm)],[c_7973,c_5723])).

cnf(c_1726,plain,
    ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_582,c_1721])).

cnf(c_5262,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1726,c_5249])).

cnf(c_5281,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_5262,c_1721])).

cnf(c_8011,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_7992,c_5281])).

cnf(c_8046,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_7964,c_8011])).

cnf(c_5585,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_5295,c_5577])).

cnf(c_7995,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_7973,c_5585])).

cnf(c_7965,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5585,c_5448])).

cnf(c_8042,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_7965,c_7995,c_8011])).

cnf(c_8043,plain,
    ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_8042,c_8011])).

cnf(c_8047,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_8046,c_7995,c_8011,c_8043])).

cnf(c_16,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1071,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_824,c_16])).

cnf(c_1238,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_658,c_1071])).

cnf(c_1759,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_1724,c_1238])).

cnf(c_3345,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_2763,c_1759])).

cnf(c_7985,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_7973,c_3345])).

cnf(c_8049,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_8047,c_7985])).

cnf(c_8051,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8049])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:22:06 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 3.34/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.98  
% 3.34/0.98  ------  iProver source info
% 3.34/0.98  
% 3.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.98  git: non_committed_changes: false
% 3.34/0.98  git: last_make_outside_of_git: false
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     num_symb
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       true
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  ------ Parsing...
% 3.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.98  ------ Proving...
% 3.34/0.98  ------ Problem Properties 
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  clauses                                 17
% 3.34/0.98  conjectures                             1
% 3.34/0.98  EPR                                     0
% 3.34/0.98  Horn                                    17
% 3.34/0.98  unary                                   7
% 3.34/0.98  binary                                  4
% 3.34/0.98  lits                                    33
% 3.34/0.98  lits eq                                 14
% 3.34/0.98  fd_pure                                 0
% 3.34/0.98  fd_pseudo                               0
% 3.34/0.98  fd_cond                                 0
% 3.34/0.98  fd_pseudo_cond                          0
% 3.34/0.98  AC symbols                              0
% 3.34/0.98  
% 3.34/0.98  ------ Schedule dynamic 5 is on 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  Current options:
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     none
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       false
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ Proving...
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS status Theorem for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98   Resolution empty clause
% 3.34/0.98  
% 3.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  fof(f2,axiom,(
% 3.34/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f42,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f2])).
% 3.34/0.98  
% 3.34/0.98  fof(f3,axiom,(
% 3.34/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f43,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f3])).
% 3.34/0.98  
% 3.34/0.98  fof(f4,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f44,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f4])).
% 3.34/0.98  
% 3.34/0.98  fof(f5,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f45,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f5])).
% 3.34/0.98  
% 3.34/0.98  fof(f6,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f46,plain,(
% 3.34/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f6])).
% 3.34/0.98  
% 3.34/0.98  fof(f7,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f47,plain,(
% 3.34/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f7])).
% 3.34/0.98  
% 3.34/0.98  fof(f8,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f48,plain,(
% 3.34/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f8])).
% 3.34/0.98  
% 3.34/0.98  fof(f65,plain,(
% 3.34/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f47,f48])).
% 3.34/0.98  
% 3.34/0.98  fof(f66,plain,(
% 3.34/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f46,f65])).
% 3.34/0.98  
% 3.34/0.98  fof(f67,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f45,f66])).
% 3.34/0.98  
% 3.34/0.98  fof(f68,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f44,f67])).
% 3.34/0.98  
% 3.34/0.98  fof(f69,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f43,f68])).
% 3.34/0.98  
% 3.34/0.98  fof(f70,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f42,f69,f69])).
% 3.34/0.98  
% 3.34/0.98  fof(f11,axiom,(
% 3.34/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f51,plain,(
% 3.34/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f11])).
% 3.34/0.98  
% 3.34/0.98  fof(f21,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f36,plain,(
% 3.34/0.98    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f21])).
% 3.34/0.98  
% 3.34/0.98  fof(f62,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f36])).
% 3.34/0.98  
% 3.34/0.98  fof(f1,axiom,(
% 3.34/0.98    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f41,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f1])).
% 3.34/0.98  
% 3.34/0.98  fof(f72,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f62,f41])).
% 3.34/0.98  
% 3.34/0.98  fof(f16,axiom,(
% 3.34/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f56,plain,(
% 3.34/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.34/0.98    inference(cnf_transformation,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f9,axiom,(
% 3.34/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f49,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f9])).
% 3.34/0.98  
% 3.34/0.98  fof(f71,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.34/0.98    inference(definition_unfolding,[],[f49,f41,f69])).
% 3.34/0.98  
% 3.34/0.98  fof(f12,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f27,plain,(
% 3.34/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f12])).
% 3.34/0.98  
% 3.34/0.98  fof(f52,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f27])).
% 3.34/0.98  
% 3.34/0.98  fof(f22,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f37,plain,(
% 3.34/0.98    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f22])).
% 3.34/0.98  
% 3.34/0.98  fof(f63,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f37])).
% 3.34/0.98  
% 3.34/0.98  fof(f14,axiom,(
% 3.34/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f29,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f14])).
% 3.34/0.98  
% 3.34/0.98  fof(f54,plain,(
% 3.34/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f29])).
% 3.34/0.98  
% 3.34/0.98  fof(f18,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f31,plain,(
% 3.34/0.98    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f18])).
% 3.34/0.98  
% 3.34/0.98  fof(f32,plain,(
% 3.34/0.98    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(flattening,[],[f31])).
% 3.34/0.98  
% 3.34/0.98  fof(f59,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f32])).
% 3.34/0.98  
% 3.34/0.98  fof(f10,axiom,(
% 3.34/0.98    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f25,plain,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f10])).
% 3.34/0.98  
% 3.34/0.98  fof(f26,plain,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.34/0.98    inference(flattening,[],[f25])).
% 3.34/0.98  
% 3.34/0.98  fof(f50,plain,(
% 3.34/0.98    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f26])).
% 3.34/0.98  
% 3.34/0.98  fof(f20,axiom,(
% 3.34/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f35,plain,(
% 3.34/0.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f20])).
% 3.34/0.98  
% 3.34/0.98  fof(f61,plain,(
% 3.34/0.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f35])).
% 3.34/0.98  
% 3.34/0.98  fof(f57,plain,(
% 3.34/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.34/0.98    inference(cnf_transformation,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f13,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f28,plain,(
% 3.34/0.98    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f13])).
% 3.34/0.98  
% 3.34/0.98  fof(f53,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f28])).
% 3.34/0.98  
% 3.34/0.98  fof(f19,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f33,plain,(
% 3.34/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f19])).
% 3.34/0.98  
% 3.34/0.98  fof(f34,plain,(
% 3.34/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(flattening,[],[f33])).
% 3.34/0.98  
% 3.34/0.98  fof(f60,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f34])).
% 3.34/0.98  
% 3.34/0.98  fof(f23,conjecture,(
% 3.34/0.98    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f24,negated_conjecture,(
% 3.34/0.98    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.34/0.98    inference(negated_conjecture,[],[f23])).
% 3.34/0.98  
% 3.34/0.98  fof(f38,plain,(
% 3.34/0.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f24])).
% 3.34/0.98  
% 3.34/0.98  fof(f39,plain,(
% 3.34/0.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f40,plain,(
% 3.34/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f39])).
% 3.34/0.98  
% 3.34/0.98  fof(f64,plain,(
% 3.34/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.34/0.98    inference(cnf_transformation,[],[f40])).
% 3.34/0.98  
% 3.34/0.98  fof(f73,plain,(
% 3.34/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.34/0.98    inference(definition_unfolding,[],[f64,f41])).
% 3.34/0.98  
% 3.34/0.98  cnf(c_0,plain,
% 3.34/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3,plain,
% 3.34/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_423,plain,
% 3.34/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_14,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0)
% 3.34/0.98      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_415,plain,
% 3.34/0.98      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_823,plain,
% 3.34/0.98      ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_423,c_415]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9,plain,
% 3.34/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_824,plain,
% 3.34/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_823,c_9]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1,plain,
% 3.34/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1069,plain,
% 3.34/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_824,c_1]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_422,plain,
% 3.34/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1721,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_423,c_422]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_15,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_414,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.34/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_658,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_423,c_414]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1724,plain,
% 3.34/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_1721,c_658]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2132,plain,
% 3.34/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_1069,c_1724]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2136,plain,
% 3.34/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_0,c_2132]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2763,plain,
% 3.34/0.98      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2136,c_2132]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.34/0.98      | ~ v1_relat_1(X1)
% 3.34/0.98      | ~ v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_420,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.34/0.98      | v1_relat_1(X0) != iProver_top
% 3.34/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3769,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 3.34/0.98      | v1_relat_1(X1) != iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_9,c_420]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_47,plain,
% 3.34/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5174,plain,
% 3.34/0.98      ( v1_relat_1(X1) != iProver_top
% 3.34/0.98      | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3769,c_47]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5175,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 3.34/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_5174]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5182,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1721,c_5175]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5295,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5182,c_47]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5302,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2763,c_5295]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_11,plain,
% 3.34/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_418,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 3.34/0.98      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.34/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3638,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 3.34/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_9,c_418]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3657,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
% 3.34/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3638,c_1721]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5576,plain,
% 3.34/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.34/0.98      | k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0) ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3657,c_47]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5577,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
% 3.34/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_5576]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5586,plain,
% 3.34/0.98      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5302,c_5577]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6512,plain,
% 3.34/0.98      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2763,c_5586]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_424,plain,
% 3.34/0.98      ( v1_relat_1(X0) != iProver_top
% 3.34/0.98      | v1_relat_1(X1) != iProver_top
% 3.34/0.98      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2771,plain,
% 3.34/0.98      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1721,c_424]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5432,plain,
% 3.34/0.98      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2771,c_47]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5438,plain,
% 3.34/0.98      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
% 3.34/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_5432,c_423]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_13,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_416,plain,
% 3.34/0.98      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_581,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_423,c_416]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8,plain,
% 3.34/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_582,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_581,c_8]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3768,plain,
% 3.34/0.98      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0))) = iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_582,c_420]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3802,plain,
% 3.34/0.98      ( r1_tarski(X0,X0) = iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_3768,c_9]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3831,plain,
% 3.34/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3802,c_47]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3838,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3831,c_418]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5448,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5438,c_3838]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7964,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X0)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_6512,c_5448]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0)
% 3.34/0.98      | ~ v1_relat_1(X1)
% 3.34/0.98      | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_421,plain,
% 3.34/0.98      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
% 3.34/0.98      | v1_relat_1(X1) != iProver_top
% 3.34/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5215,plain,
% 3.34/0.98      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
% 3.34/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_423,c_421]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5247,plain,
% 3.34/0.98      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_423,c_5215]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5249,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_5247,c_1721]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7971,plain,
% 3.34/0.98      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5448,c_5249]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_12,plain,
% 3.34/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_417,plain,
% 3.34/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1917,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 3.34/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_8,c_417]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1918,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 3.34/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.34/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_1917,c_1721]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5075,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 3.34/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.34/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1918,c_423]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5358,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5302,c_5075]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5796,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2763,c_5358]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7973,plain,
% 3.34/0.98      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7971,c_5796]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5309,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5295,c_5075]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5723,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2763,c_5309]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7992,plain,
% 3.34/0.98      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7973,c_5723]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1726,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_582,c_1721]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5262,plain,
% 3.34/0.98      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1726,c_5249]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5281,plain,
% 3.34/0.98      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_5262,c_1721]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8011,plain,
% 3.34/0.98      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_7992,c_5281]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8046,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_7964,c_8011]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5585,plain,
% 3.34/0.98      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5295,c_5577]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7995,plain,
% 3.34/0.98      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7973,c_5585]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7965,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5585,c_5448]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8042,plain,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_7965,c_7995,c_8011]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8043,plain,
% 3.34/0.98      ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_8042,c_8011]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8047,plain,
% 3.34/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_8046,c_7995,c_8011,c_8043]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_16,negated_conjecture,
% 3.34/0.98      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1071,plain,
% 3.34/0.98      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_824,c_16]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1238,plain,
% 3.34/0.98      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_658,c_1071]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1759,plain,
% 3.34/0.98      ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_1724,c_1238]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3345,plain,
% 3.34/0.98      ( k6_relat_1(k1_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_2763,c_1759]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7985,plain,
% 3.34/0.98      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7973,c_3345]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8049,plain,
% 3.34/0.98      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK1,k6_relat_1(sK0)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_8047,c_7985]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8051,plain,
% 3.34/0.98      ( $false ),
% 3.34/0.98      inference(equality_resolution_simp,[status(thm)],[c_8049]) ).
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  ------                               Statistics
% 3.34/0.98  
% 3.34/0.98  ------ General
% 3.34/0.98  
% 3.34/0.98  abstr_ref_over_cycles:                  0
% 3.34/0.98  abstr_ref_under_cycles:                 0
% 3.34/0.98  gc_basic_clause_elim:                   0
% 3.34/0.98  forced_gc_time:                         0
% 3.34/0.98  parsing_time:                           0.011
% 3.34/0.98  unif_index_cands_time:                  0.
% 3.34/0.98  unif_index_add_time:                    0.
% 3.34/0.98  orderings_time:                         0.
% 3.34/0.98  out_proof_time:                         0.011
% 3.34/0.98  total_time:                             0.26
% 3.34/0.98  num_of_symbols:                         45
% 3.34/0.98  num_of_terms:                           12097
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing
% 3.34/0.98  
% 3.34/0.98  num_of_splits:                          0
% 3.34/0.98  num_of_split_atoms:                     0
% 3.34/0.98  num_of_reused_defs:                     0
% 3.34/0.98  num_eq_ax_congr_red:                    22
% 3.34/0.98  num_of_sem_filtered_clauses:            1
% 3.34/0.98  num_of_subtypes:                        0
% 3.34/0.98  monotx_restored_types:                  0
% 3.34/0.98  sat_num_of_epr_types:                   0
% 3.34/0.98  sat_num_of_non_cyclic_types:            0
% 3.34/0.98  sat_guarded_non_collapsed_types:        0
% 3.34/0.98  num_pure_diseq_elim:                    0
% 3.34/0.98  simp_replaced_by:                       0
% 3.34/0.98  res_preprocessed:                       76
% 3.34/0.98  prep_upred:                             0
% 3.34/0.98  prep_unflattend:                        2
% 3.34/0.98  smt_new_axioms:                         0
% 3.34/0.98  pred_elim_cands:                        2
% 3.34/0.98  pred_elim:                              0
% 3.34/0.98  pred_elim_cl:                           0
% 3.34/0.98  pred_elim_cycles:                       1
% 3.34/0.98  merged_defs:                            0
% 3.34/0.98  merged_defs_ncl:                        0
% 3.34/0.98  bin_hyper_res:                          0
% 3.34/0.98  prep_cycles:                            3
% 3.34/0.98  pred_elim_time:                         0.001
% 3.34/0.98  splitting_time:                         0.
% 3.34/0.98  sem_filter_time:                        0.
% 3.34/0.98  monotx_time:                            0.
% 3.34/0.98  subtype_inf_time:                       0.
% 3.34/0.98  
% 3.34/0.98  ------ Problem properties
% 3.34/0.98  
% 3.34/0.98  clauses:                                17
% 3.34/0.98  conjectures:                            1
% 3.34/0.98  epr:                                    0
% 3.34/0.98  horn:                                   17
% 3.34/0.98  ground:                                 1
% 3.34/0.98  unary:                                  7
% 3.34/0.98  binary:                                 4
% 3.34/0.98  lits:                                   33
% 3.34/0.98  lits_eq:                                14
% 3.34/0.98  fd_pure:                                0
% 3.34/0.98  fd_pseudo:                              0
% 3.34/0.98  fd_cond:                                0
% 3.34/0.98  fd_pseudo_cond:                         0
% 3.34/0.98  ac_symbols:                             0
% 3.34/0.98  
% 3.34/0.98  ------ Propositional Solver
% 3.34/0.98  
% 3.34/0.98  prop_solver_calls:                      24
% 3.34/0.98  prop_fast_solver_calls:                 469
% 3.34/0.98  smt_solver_calls:                       0
% 3.34/0.98  smt_fast_solver_calls:                  0
% 3.34/0.98  prop_num_of_clauses:                    3293
% 3.34/0.98  prop_preprocess_simplified:             6608
% 3.34/0.98  prop_fo_subsumed:                       5
% 3.34/0.98  prop_solver_time:                       0.
% 3.34/0.98  smt_solver_time:                        0.
% 3.34/0.98  smt_fast_solver_time:                   0.
% 3.34/0.98  prop_fast_solver_time:                  0.
% 3.34/0.98  prop_unsat_core_time:                   0.
% 3.34/0.98  
% 3.34/0.98  ------ QBF
% 3.34/0.98  
% 3.34/0.98  qbf_q_res:                              0
% 3.34/0.98  qbf_num_tautologies:                    0
% 3.34/0.98  qbf_prep_cycles:                        0
% 3.34/0.98  
% 3.34/0.98  ------ BMC1
% 3.34/0.98  
% 3.34/0.98  bmc1_current_bound:                     -1
% 3.34/0.98  bmc1_last_solved_bound:                 -1
% 3.34/0.98  bmc1_unsat_core_size:                   -1
% 3.34/0.98  bmc1_unsat_core_parents_size:           -1
% 3.34/0.98  bmc1_merge_next_fun:                    0
% 3.34/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation
% 3.34/0.98  
% 3.34/0.98  inst_num_of_clauses:                    917
% 3.34/0.98  inst_num_in_passive:                    76
% 3.34/0.98  inst_num_in_active:                     438
% 3.34/0.98  inst_num_in_unprocessed:                403
% 3.34/0.98  inst_num_of_loops:                      460
% 3.34/0.98  inst_num_of_learning_restarts:          0
% 3.34/0.98  inst_num_moves_active_passive:          21
% 3.34/0.98  inst_lit_activity:                      0
% 3.34/0.98  inst_lit_activity_moves:                1
% 3.34/0.98  inst_num_tautologies:                   0
% 3.34/0.98  inst_num_prop_implied:                  0
% 3.34/0.98  inst_num_existing_simplified:           0
% 3.34/0.98  inst_num_eq_res_simplified:             0
% 3.34/0.98  inst_num_child_elim:                    0
% 3.34/0.98  inst_num_of_dismatching_blockings:      212
% 3.34/0.98  inst_num_of_non_proper_insts:           461
% 3.34/0.98  inst_num_of_duplicates:                 0
% 3.34/0.98  inst_inst_num_from_inst_to_res:         0
% 3.34/0.98  inst_dismatching_checking_time:         0.
% 3.34/0.98  
% 3.34/0.98  ------ Resolution
% 3.34/0.98  
% 3.34/0.98  res_num_of_clauses:                     0
% 3.34/0.98  res_num_in_passive:                     0
% 3.34/0.98  res_num_in_active:                      0
% 3.34/0.98  res_num_of_loops:                       79
% 3.34/0.98  res_forward_subset_subsumed:            60
% 3.34/0.98  res_backward_subset_subsumed:           0
% 3.34/0.98  res_forward_subsumed:                   0
% 3.34/0.98  res_backward_subsumed:                  0
% 3.34/0.98  res_forward_subsumption_resolution:     0
% 3.34/0.98  res_backward_subsumption_resolution:    0
% 3.34/0.98  res_clause_to_clause_subsumption:       1135
% 3.34/0.98  res_orphan_elimination:                 0
% 3.34/0.98  res_tautology_del:                      42
% 3.34/0.98  res_num_eq_res_simplified:              0
% 3.34/0.98  res_num_sel_changes:                    0
% 3.34/0.98  res_moves_from_active_to_pass:          0
% 3.34/0.98  
% 3.34/0.98  ------ Superposition
% 3.34/0.98  
% 3.34/0.98  sup_time_total:                         0.
% 3.34/0.98  sup_time_generating:                    0.
% 3.34/0.98  sup_time_sim_full:                      0.
% 3.34/0.98  sup_time_sim_immed:                     0.
% 3.34/0.98  
% 3.34/0.98  sup_num_of_clauses:                     223
% 3.34/0.98  sup_num_in_active:                      61
% 3.34/0.98  sup_num_in_passive:                     162
% 3.34/0.98  sup_num_of_loops:                       90
% 3.34/0.98  sup_fw_superposition:                   508
% 3.34/0.98  sup_bw_superposition:                   540
% 3.34/0.98  sup_immediate_simplified:               504
% 3.34/0.98  sup_given_eliminated:                   1
% 3.34/0.98  comparisons_done:                       0
% 3.34/0.98  comparisons_avoided:                    0
% 3.34/0.98  
% 3.34/0.98  ------ Simplifications
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  sim_fw_subset_subsumed:                 1
% 3.34/0.98  sim_bw_subset_subsumed:                 2
% 3.34/0.98  sim_fw_subsumed:                        82
% 3.34/0.98  sim_bw_subsumed:                        0
% 3.34/0.98  sim_fw_subsumption_res:                 2
% 3.34/0.98  sim_bw_subsumption_res:                 0
% 3.34/0.98  sim_tautology_del:                      3
% 3.34/0.98  sim_eq_tautology_del:                   141
% 3.34/0.98  sim_eq_res_simp:                        0
% 3.34/0.98  sim_fw_demodulated:                     248
% 3.34/0.98  sim_bw_demodulated:                     33
% 3.34/0.98  sim_light_normalised:                   326
% 3.34/0.98  sim_joinable_taut:                      0
% 3.34/0.98  sim_joinable_simp:                      0
% 3.34/0.98  sim_ac_normalised:                      0
% 3.34/0.98  sim_smt_subsumption:                    0
% 3.34/0.98  
%------------------------------------------------------------------------------
