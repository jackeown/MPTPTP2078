%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:06 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  168 (6808 expanded)
%              Number of clauses        :   96 (2996 expanded)
%              Number of leaves         :   23 (1417 expanded)
%              Depth                    :   31
%              Number of atoms          :  287 (10938 expanded)
%              Number of equality atoms :  189 (6001 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f72])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f43,f73])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f40,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).

fof(f67,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f67,f73])).

cnf(c_2,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_648,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_637,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1172,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_648,c_637])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1173,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1172,c_9])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_650,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1849,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1173,c_650])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_640,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2426,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_640])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_636,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_911,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_648,c_636])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_649,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2381,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_649])).

cnf(c_56,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5623,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2381,c_56])).

cnf(c_5629,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5623,c_648])).

cnf(c_6252,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2426,c_5629])).

cnf(c_5639,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_5629,c_636])).

cnf(c_6265,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_6252,c_5639])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_647,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4200,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_647])).

cnf(c_6128,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_648,c_4200])).

cnf(c_6134,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_6128,c_911])).

cnf(c_11,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_641,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6395,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6134,c_641])).

cnf(c_7659,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6395,c_5629])).

cnf(c_7661,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_7659])).

cnf(c_2428,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_640])).

cnf(c_2432,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2428,c_911])).

cnf(c_6754,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2432,c_56])).

cnf(c_6755,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6754])).

cnf(c_7786,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_7661,c_6755])).

cnf(c_10147,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0))),k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_7786,c_7786])).

cnf(c_1178,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_641])).

cnf(c_3775,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1178,c_648])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_639,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2258,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_639])).

cnf(c_2262,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2258,c_911])).

cnf(c_3941,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2262,c_648])).

cnf(c_3946,plain,
    ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_3775,c_3941])).

cnf(c_10152,plain,
    ( k7_relat_1(k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_7786,c_3946])).

cnf(c_10176,plain,
    ( k7_relat_1(k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(demodulation,[status(thm)],[c_10152,c_7786])).

cnf(c_10185,plain,
    ( k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(light_normalisation,[status(thm)],[c_10147,c_7786,c_10176])).

cnf(c_10747,plain,
    ( k1_relat_1(k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_10185,c_9])).

cnf(c_11195,plain,
    ( k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_10747,c_9])).

cnf(c_11570,plain,
    ( k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_11195,c_9])).

cnf(c_12114,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_11570,c_9])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_644,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3083,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_644])).

cnf(c_3122,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3083,c_648])).

cnf(c_3126,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_3122])).

cnf(c_3859,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3126,c_648])).

cnf(c_3952,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_3859,c_3941])).

cnf(c_12351,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_12114,c_3952])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_645,plain,
    ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4224,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_645])).

cnf(c_6151,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_648,c_4224])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_646,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1329,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_648,c_646])).

cnf(c_1330,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1329,c_911])).

cnf(c_6157,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_6151,c_911,c_1330,c_5639])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_638,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5646,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_5629,c_638])).

cnf(c_5645,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_5629,c_646])).

cnf(c_5810,plain,
    ( k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_5646,c_5645])).

cnf(c_6344,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_6157,c_5810])).

cnf(c_6320,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_3952,c_6265])).

cnf(c_6322,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_6320,c_3952])).

cnf(c_7133,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_6344,c_6322])).

cnf(c_12384,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_12114,c_7133])).

cnf(c_12431,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_12351,c_12384])).

cnf(c_13477,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_12431,c_9])).

cnf(c_17,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_914,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_911,c_17])).

cnf(c_1851,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1173,c_914])).

cnf(c_12161,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_12114,c_1851])).

cnf(c_14361,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_13477,c_12161])).

cnf(c_12360,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12114,c_3859])).

cnf(c_13047,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_12360,c_6755])).

cnf(c_13052,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_13047,c_7133])).

cnf(c_14363,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_14361,c_13052])).

cnf(c_14926,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14363,c_12114])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.70/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.00  
% 3.70/1.00  ------  iProver source info
% 3.70/1.00  
% 3.70/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.00  git: non_committed_changes: false
% 3.70/1.00  git: last_make_outside_of_git: false
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    --mode clausify
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         false
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     num_symb
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       true
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     false
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   []
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_full_bw                           [BwDemod]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  ------ Parsing...
% 3.70/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.00  ------ Proving...
% 3.70/1.00  ------ Problem Properties 
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  clauses                                 18
% 3.70/1.00  conjectures                             1
% 3.70/1.00  EPR                                     0
% 3.70/1.00  Horn                                    18
% 3.70/1.00  unary                                   5
% 3.70/1.00  binary                                  6
% 3.70/1.00  lits                                    39
% 3.70/1.00  lits eq                                 12
% 3.70/1.00  fd_pure                                 0
% 3.70/1.00  fd_pseudo                               0
% 3.70/1.00  fd_cond                                 0
% 3.70/1.00  fd_pseudo_cond                          0
% 3.70/1.00  AC symbols                              0
% 3.70/1.00  
% 3.70/1.00  ------ Schedule dynamic 5 is on 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  Current options:
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    --mode clausify
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         false
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     none
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       false
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     false
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   []
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_full_bw                           [BwDemod]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ Proving...
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS status Theorem for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00   Resolution empty clause
% 3.70/1.00  
% 3.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  fof(f10,axiom,(
% 3.70/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f52,plain,(
% 3.70/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f10])).
% 3.70/1.00  
% 3.70/1.00  fof(f21,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f38,plain,(
% 3.70/1.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f21])).
% 3.70/1.00  
% 3.70/1.00  fof(f65,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f38])).
% 3.70/1.00  
% 3.70/1.00  fof(f8,axiom,(
% 3.70/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f50,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f8])).
% 3.70/1.00  
% 3.70/1.00  fof(f2,axiom,(
% 3.70/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f44,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f2])).
% 3.70/1.00  
% 3.70/1.00  fof(f3,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f45,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f3])).
% 3.70/1.00  
% 3.70/1.00  fof(f4,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f46,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f4])).
% 3.70/1.00  
% 3.70/1.00  fof(f5,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f47,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f5])).
% 3.70/1.00  
% 3.70/1.00  fof(f6,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f48,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f6])).
% 3.70/1.00  
% 3.70/1.00  fof(f7,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f49,plain,(
% 3.70/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f7])).
% 3.70/1.00  
% 3.70/1.00  fof(f68,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f48,f49])).
% 3.70/1.00  
% 3.70/1.00  fof(f69,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f47,f68])).
% 3.70/1.00  
% 3.70/1.00  fof(f70,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f46,f69])).
% 3.70/1.00  
% 3.70/1.00  fof(f71,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f45,f70])).
% 3.70/1.00  
% 3.70/1.00  fof(f72,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f44,f71])).
% 3.70/1.00  
% 3.70/1.00  fof(f73,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.70/1.00    inference(definition_unfolding,[],[f50,f72])).
% 3.70/1.00  
% 3.70/1.00  fof(f75,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f65,f73])).
% 3.70/1.00  
% 3.70/1.00  fof(f16,axiom,(
% 3.70/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f58,plain,(
% 3.70/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f16])).
% 3.70/1.00  
% 3.70/1.00  fof(f1,axiom,(
% 3.70/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f43,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f1])).
% 3.70/1.00  
% 3.70/1.00  fof(f74,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f43,f73])).
% 3.70/1.00  
% 3.70/1.00  fof(f18,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f33,plain,(
% 3.70/1.00    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f18])).
% 3.70/1.00  
% 3.70/1.00  fof(f34,plain,(
% 3.70/1.00    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(flattening,[],[f33])).
% 3.70/1.00  
% 3.70/1.00  fof(f62,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f34])).
% 3.70/1.00  
% 3.70/1.00  fof(f22,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f39,plain,(
% 3.70/1.00    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f22])).
% 3.70/1.00  
% 3.70/1.00  fof(f66,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f39])).
% 3.70/1.00  
% 3.70/1.00  fof(f9,axiom,(
% 3.70/1.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f25,plain,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.70/1.00    inference(ennf_transformation,[],[f9])).
% 3.70/1.00  
% 3.70/1.00  fof(f26,plain,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.70/1.00    inference(flattening,[],[f25])).
% 3.70/1.00  
% 3.70/1.00  fof(f51,plain,(
% 3.70/1.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f26])).
% 3.70/1.00  
% 3.70/1.00  fof(f11,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f27,plain,(
% 3.70/1.00    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f11])).
% 3.70/1.00  
% 3.70/1.00  fof(f53,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f27])).
% 3.70/1.00  
% 3.70/1.00  fof(f17,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f32,plain,(
% 3.70/1.00    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f17])).
% 3.70/1.00  
% 3.70/1.00  fof(f60,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f32])).
% 3.70/1.00  
% 3.70/1.00  fof(f59,plain,(
% 3.70/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f16])).
% 3.70/1.00  
% 3.70/1.00  fof(f19,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f35,plain,(
% 3.70/1.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f19])).
% 3.70/1.00  
% 3.70/1.00  fof(f36,plain,(
% 3.70/1.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(flattening,[],[f35])).
% 3.70/1.00  
% 3.70/1.00  fof(f63,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f36])).
% 3.70/1.00  
% 3.70/1.00  fof(f14,axiom,(
% 3.70/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f30,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f14])).
% 3.70/1.00  
% 3.70/1.00  fof(f56,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f30])).
% 3.70/1.00  
% 3.70/1.00  fof(f13,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f29,plain,(
% 3.70/1.00    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f13])).
% 3.70/1.00  
% 3.70/1.00  fof(f55,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f29])).
% 3.70/1.00  
% 3.70/1.00  fof(f12,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f28,plain,(
% 3.70/1.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f12])).
% 3.70/1.00  
% 3.70/1.00  fof(f54,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f28])).
% 3.70/1.00  
% 3.70/1.00  fof(f20,axiom,(
% 3.70/1.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f37,plain,(
% 3.70/1.00    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f20])).
% 3.70/1.00  
% 3.70/1.00  fof(f64,plain,(
% 3.70/1.00    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f37])).
% 3.70/1.00  
% 3.70/1.00  fof(f23,conjecture,(
% 3.70/1.00    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f24,negated_conjecture,(
% 3.70/1.00    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.70/1.00    inference(negated_conjecture,[],[f23])).
% 3.70/1.00  
% 3.70/1.00  fof(f40,plain,(
% 3.70/1.00    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f24])).
% 3.70/1.00  
% 3.70/1.00  fof(f41,plain,(
% 3.70/1.00    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f42,plain,(
% 3.70/1.00    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).
% 3.70/1.00  
% 3.70/1.00  fof(f67,plain,(
% 3.70/1.00    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.70/1.00    inference(cnf_transformation,[],[f42])).
% 3.70/1.00  
% 3.70/1.00  fof(f76,plain,(
% 3.70/1.00    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 3.70/1.00    inference(definition_unfolding,[],[f67,f73])).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2,plain,
% 3.70/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_648,plain,
% 3.70/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_15,plain,
% 3.70/1.00      ( ~ v1_relat_1(X0)
% 3.70/1.00      | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_637,plain,
% 3.70/1.00      ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1172,plain,
% 3.70/1.00      ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_648,c_637]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9,plain,
% 3.70/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1173,plain,
% 3.70/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_1172,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_0,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_650,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1849,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_1173,c_650]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12,plain,
% 3.70/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_640,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 3.70/1.00      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2426,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 3.70/1.00      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1849,c_640]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_16,plain,
% 3.70/1.00      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_636,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_911,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_648,c_636]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1,plain,
% 3.70/1.00      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_649,plain,
% 3.70/1.00      ( v1_relat_1(X0) != iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top
% 3.70/1.00      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2381,plain,
% 3.70/1.00      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_911,c_649]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_56,plain,
% 3.70/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5623,plain,
% 3.70/1.00      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2381,c_56]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5629,plain,
% 3.70/1.00      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5623,c_648]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6252,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2426,c_5629]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5639,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_5629,c_636]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6265,plain,
% 3.70/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_6252,c_5639]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3,plain,
% 3.70/1.00      ( ~ v1_relat_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X1)
% 3.70/1.00      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_647,plain,
% 3.70/1.00      ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
% 3.70/1.00      | v1_relat_1(X0) != iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4200,plain,
% 3.70/1.00      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_648,c_647]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6128,plain,
% 3.70/1.00      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_648,c_4200]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6134,plain,
% 3.70/1.00      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_6128,c_911]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11,plain,
% 3.70/1.00      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_641,plain,
% 3.70/1.00      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6395,plain,
% 3.70/1.00      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 3.70/1.00      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_6134,c_641]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7659,plain,
% 3.70/1.00      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6395,c_5629]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7661,plain,
% 3.70/1.00      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_6265,c_7659]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2428,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 3.70/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_9,c_640]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2432,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.70/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_2428,c_911]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6754,plain,
% 3.70/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.70/1.00      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.70/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2432,c_56]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6755,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.70/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_6754]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7786,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_7661,c_6755]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10147,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0))),k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_7786,c_7786]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1178,plain,
% 3.70/1.00      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_911,c_641]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3775,plain,
% 3.70/1.00      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1178,c_648]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8,plain,
% 3.70/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13,plain,
% 3.70/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_639,plain,
% 3.70/1.00      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.70/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2258,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 3.70/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_8,c_639]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2262,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 3.70/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_2258,c_911]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3941,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 3.70/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2262,c_648]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3946,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_3775,c_3941]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10152,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_7786,c_3946]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10176,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_10152,c_7786]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10185,plain,
% 3.70/1.00      ( k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_10147,c_7786,c_10176]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10747,plain,
% 3.70/1.00      ( k1_relat_1(k6_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_10185,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11195,plain,
% 3.70/1.00      ( k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_10747,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11570,plain,
% 3.70/1.00      ( k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_11195,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12114,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_11570,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.70/1.00      | ~ v1_relat_1(X1)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_644,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3083,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_8,c_644]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3122,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3083,c_648]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3126,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 3.70/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_911,c_3122]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3859,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3126,c_648]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3952,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_3859,c_3941]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12351,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12114,c_3952]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5,plain,
% 3.70/1.00      ( ~ v1_relat_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X1)
% 3.70/1.00      | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_645,plain,
% 3.70/1.00      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
% 3.70/1.00      | v1_relat_1(X1) != iProver_top
% 3.70/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4224,plain,
% 3.70/1.00      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
% 3.70/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_648,c_645]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6151,plain,
% 3.70/1.00      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_648,c_4224]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4,plain,
% 3.70/1.00      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_646,plain,
% 3.70/1.00      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1329,plain,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_648,c_646]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1330,plain,
% 3.70/1.00      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_1329,c_911]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6157,plain,
% 3.70/1.00      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_6151,c_911,c_1330,c_5639]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14,plain,
% 3.70/1.00      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_638,plain,
% 3.70/1.00      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5646,plain,
% 3.70/1.00      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_5629,c_638]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5645,plain,
% 3.70/1.00      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_5629,c_646]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5810,plain,
% 3.70/1.00      ( k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_5646,c_5645]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6344,plain,
% 3.70/1.00      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_6157,c_5810]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6320,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_3952,c_6265]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6322,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_6320,c_3952]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_7133,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_6344,c_6322]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12384,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12114,c_7133]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12431,plain,
% 3.70/1.00      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_12351,c_12384]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13477,plain,
% 3.70/1.00      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12431,c_9]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_17,negated_conjecture,
% 3.70/1.00      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_914,plain,
% 3.70/1.00      ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_911,c_17]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1851,plain,
% 3.70/1.00      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_1173,c_914]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12161,plain,
% 3.70/1.00      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_12114,c_1851]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14361,plain,
% 3.70/1.00      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_13477,c_12161]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12360,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12114,c_3859]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13047,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_12360,c_6755]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13052,plain,
% 3.70/1.00      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_13047,c_7133]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14363,plain,
% 3.70/1.00      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_14361,c_13052]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14926,plain,
% 3.70/1.00      ( $false ),
% 3.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_14363,c_12114]) ).
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  ------                               Statistics
% 3.70/1.00  
% 3.70/1.00  ------ General
% 3.70/1.00  
% 3.70/1.00  abstr_ref_over_cycles:                  0
% 3.70/1.00  abstr_ref_under_cycles:                 0
% 3.70/1.00  gc_basic_clause_elim:                   0
% 3.70/1.00  forced_gc_time:                         0
% 3.70/1.00  parsing_time:                           0.01
% 3.70/1.00  unif_index_cands_time:                  0.
% 3.70/1.00  unif_index_add_time:                    0.
% 3.70/1.00  orderings_time:                         0.
% 3.70/1.00  out_proof_time:                         0.011
% 3.70/1.00  total_time:                             0.372
% 3.70/1.00  num_of_symbols:                         43
% 3.70/1.00  num_of_terms:                           20331
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing
% 3.70/1.00  
% 3.70/1.00  num_of_splits:                          0
% 3.70/1.00  num_of_split_atoms:                     0
% 3.70/1.00  num_of_reused_defs:                     0
% 3.70/1.00  num_eq_ax_congr_red:                    4
% 3.70/1.00  num_of_sem_filtered_clauses:            1
% 3.70/1.00  num_of_subtypes:                        0
% 3.70/1.00  monotx_restored_types:                  0
% 3.70/1.00  sat_num_of_epr_types:                   0
% 3.70/1.00  sat_num_of_non_cyclic_types:            0
% 3.70/1.00  sat_guarded_non_collapsed_types:        0
% 3.70/1.00  num_pure_diseq_elim:                    0
% 3.70/1.00  simp_replaced_by:                       0
% 3.70/1.00  res_preprocessed:                       79
% 3.70/1.00  prep_upred:                             0
% 3.70/1.00  prep_unflattend:                        8
% 3.70/1.00  smt_new_axioms:                         0
% 3.70/1.00  pred_elim_cands:                        2
% 3.70/1.00  pred_elim:                              0
% 3.70/1.00  pred_elim_cl:                           0
% 3.70/1.00  pred_elim_cycles:                       1
% 3.70/1.00  merged_defs:                            0
% 3.70/1.00  merged_defs_ncl:                        0
% 3.70/1.00  bin_hyper_res:                          0
% 3.70/1.00  prep_cycles:                            3
% 3.70/1.00  pred_elim_time:                         0.003
% 3.70/1.00  splitting_time:                         0.
% 3.70/1.00  sem_filter_time:                        0.
% 3.70/1.00  monotx_time:                            0.
% 3.70/1.00  subtype_inf_time:                       0.
% 3.70/1.00  
% 3.70/1.00  ------ Problem properties
% 3.70/1.00  
% 3.70/1.00  clauses:                                18
% 3.70/1.00  conjectures:                            1
% 3.70/1.00  epr:                                    0
% 3.70/1.00  horn:                                   18
% 3.70/1.00  ground:                                 1
% 3.70/1.00  unary:                                  5
% 3.70/1.00  binary:                                 6
% 3.70/1.00  lits:                                   39
% 3.70/1.00  lits_eq:                                12
% 3.70/1.00  fd_pure:                                0
% 3.70/1.00  fd_pseudo:                              0
% 3.70/1.00  fd_cond:                                0
% 3.70/1.00  fd_pseudo_cond:                         0
% 3.70/1.00  ac_symbols:                             0
% 3.70/1.00  
% 3.70/1.00  ------ Propositional Solver
% 3.70/1.00  
% 3.70/1.00  prop_solver_calls:                      26
% 3.70/1.00  prop_fast_solver_calls:                 649
% 3.70/1.00  smt_solver_calls:                       0
% 3.70/1.00  smt_fast_solver_calls:                  0
% 3.70/1.00  prop_num_of_clauses:                    5234
% 3.70/1.00  prop_preprocess_simplified:             8362
% 3.70/1.00  prop_fo_subsumed:                       8
% 3.70/1.00  prop_solver_time:                       0.
% 3.70/1.00  smt_solver_time:                        0.
% 3.70/1.00  smt_fast_solver_time:                   0.
% 3.70/1.00  prop_fast_solver_time:                  0.
% 3.70/1.00  prop_unsat_core_time:                   0.
% 3.70/1.00  
% 3.70/1.00  ------ QBF
% 3.70/1.00  
% 3.70/1.00  qbf_q_res:                              0
% 3.70/1.00  qbf_num_tautologies:                    0
% 3.70/1.00  qbf_prep_cycles:                        0
% 3.70/1.00  
% 3.70/1.00  ------ BMC1
% 3.70/1.00  
% 3.70/1.00  bmc1_current_bound:                     -1
% 3.70/1.00  bmc1_last_solved_bound:                 -1
% 3.70/1.00  bmc1_unsat_core_size:                   -1
% 3.70/1.00  bmc1_unsat_core_parents_size:           -1
% 3.70/1.00  bmc1_merge_next_fun:                    0
% 3.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation
% 3.70/1.01  
% 3.70/1.01  inst_num_of_clauses:                    1269
% 3.70/1.01  inst_num_in_passive:                    403
% 3.70/1.01  inst_num_in_active:                     669
% 3.70/1.01  inst_num_in_unprocessed:                197
% 3.70/1.01  inst_num_of_loops:                      710
% 3.70/1.01  inst_num_of_learning_restarts:          0
% 3.70/1.01  inst_num_moves_active_passive:          39
% 3.70/1.01  inst_lit_activity:                      0
% 3.70/1.01  inst_lit_activity_moves:                1
% 3.70/1.01  inst_num_tautologies:                   0
% 3.70/1.01  inst_num_prop_implied:                  0
% 3.70/1.01  inst_num_existing_simplified:           0
% 3.70/1.01  inst_num_eq_res_simplified:             0
% 3.70/1.01  inst_num_child_elim:                    0
% 3.70/1.01  inst_num_of_dismatching_blockings:      864
% 3.70/1.01  inst_num_of_non_proper_insts:           860
% 3.70/1.01  inst_num_of_duplicates:                 0
% 3.70/1.01  inst_inst_num_from_inst_to_res:         0
% 3.70/1.01  inst_dismatching_checking_time:         0.
% 3.70/1.01  
% 3.70/1.01  ------ Resolution
% 3.70/1.01  
% 3.70/1.01  res_num_of_clauses:                     0
% 3.70/1.01  res_num_in_passive:                     0
% 3.70/1.01  res_num_in_active:                      0
% 3.70/1.01  res_num_of_loops:                       82
% 3.70/1.01  res_forward_subset_subsumed:            100
% 3.70/1.01  res_backward_subset_subsumed:           0
% 3.70/1.01  res_forward_subsumed:                   0
% 3.70/1.01  res_backward_subsumed:                  0
% 3.70/1.01  res_forward_subsumption_resolution:     0
% 3.70/1.01  res_backward_subsumption_resolution:    0
% 3.70/1.01  res_clause_to_clause_subsumption:       3449
% 3.70/1.01  res_orphan_elimination:                 0
% 3.70/1.01  res_tautology_del:                      111
% 3.70/1.01  res_num_eq_res_simplified:              0
% 3.70/1.01  res_num_sel_changes:                    0
% 3.70/1.01  res_moves_from_active_to_pass:          0
% 3.70/1.01  
% 3.70/1.01  ------ Superposition
% 3.70/1.01  
% 3.70/1.01  sup_time_total:                         0.
% 3.70/1.01  sup_time_generating:                    0.
% 3.70/1.01  sup_time_sim_full:                      0.
% 3.70/1.01  sup_time_sim_immed:                     0.
% 3.70/1.01  
% 3.70/1.01  sup_num_of_clauses:                     659
% 3.70/1.01  sup_num_in_active:                      100
% 3.70/1.01  sup_num_in_passive:                     559
% 3.70/1.01  sup_num_of_loops:                       141
% 3.70/1.01  sup_fw_superposition:                   1179
% 3.70/1.01  sup_bw_superposition:                   1676
% 3.70/1.01  sup_immediate_simplified:               1083
% 3.70/1.01  sup_given_eliminated:                   0
% 3.70/1.01  comparisons_done:                       0
% 3.70/1.01  comparisons_avoided:                    0
% 3.70/1.01  
% 3.70/1.01  ------ Simplifications
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  sim_fw_subset_subsumed:                 13
% 3.70/1.01  sim_bw_subset_subsumed:                 3
% 3.70/1.01  sim_fw_subsumed:                        275
% 3.70/1.01  sim_bw_subsumed:                        0
% 3.70/1.01  sim_fw_subsumption_res:                 9
% 3.70/1.01  sim_bw_subsumption_res:                 0
% 3.70/1.01  sim_tautology_del:                      14
% 3.70/1.01  sim_eq_tautology_del:                   193
% 3.70/1.01  sim_eq_res_simp:                        0
% 3.70/1.01  sim_fw_demodulated:                     398
% 3.70/1.01  sim_bw_demodulated:                     48
% 3.70/1.01  sim_light_normalised:                   576
% 3.70/1.01  sim_joinable_taut:                      0
% 3.70/1.01  sim_joinable_simp:                      0
% 3.70/1.01  sim_ac_normalised:                      0
% 3.70/1.01  sim_smt_subsumption:                    0
% 3.70/1.01  
%------------------------------------------------------------------------------
